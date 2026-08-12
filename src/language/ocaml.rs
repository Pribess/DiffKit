use std::io;
use std::path::Path;

use tree_sitter::{Node, Parser};

use super::{FileContext, FrontendResult, LanguageFrontend};
use crate::model::{
    CallLabel, CallSite, CallSyntax, CallTarget, FileAnalysis, FunctionInfo, LanguageFact,
    LanguageId, SourceSpan, SymbolId,
};

/// OCaml syntax frontend.
///
/// It owns OCaml's native application syntax and source spans. Semantic symbol
/// IDs produced by `ocaml-index` can replace the conservative path resolution
/// later without changing the common graph, diff, or renderer.
#[derive(Default)]
pub struct OcamlFrontend;

impl LanguageFrontend for OcamlFrontend {
    fn language(&self) -> LanguageId {
        LanguageId::new("ocaml")
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["ml", "mli"]
    }

    fn analyze_file(
        &self,
        context: &FileContext<'_>,
        source: &str,
    ) -> FrontendResult<FileAnalysis> {
        let mut parser = Parser::new();
        let language = if context.path.extension().and_then(|value| value.to_str()) == Some("mli") {
            tree_sitter_ocaml::LANGUAGE_OCAML_INTERFACE
        } else {
            tree_sitter_ocaml::LANGUAGE_OCAML
        };
        parser
            .set_language(&language.into())
            .map_err(|error| io::Error::other(format!("failed to load OCaml grammar: {error}")))?;
        let tree = parser
            .parse(source, None)
            .ok_or_else(|| io::Error::other("OCaml parser returned no syntax tree"))?;
        if tree.root_node().has_error() {
            return Err(io::Error::other(format!(
                "failed to parse OCaml source: {}",
                context.path.display()
            ))
            .into());
        }

        let mut analysis = FileAnalysis::default();
        let module = context
            .module
            .iter()
            .map(|part| ocaml_module_name(part))
            .collect::<Vec<_>>();
        analyze_structure(
            context.path,
            &module,
            tree.root_node(),
            source,
            &mut analysis,
        );
        Ok(analysis)
    }
}

fn ocaml_module_name(value: &str) -> String {
    let mut characters = value.chars();
    let Some(first) = characters.next() else {
        return String::new();
    };
    first.to_uppercase().chain(characters).collect()
}

fn analyze_structure(
    file: &Path,
    module: &[String],
    structure: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
) {
    let mut cursor = structure.walk();
    for child in structure.named_children(&mut cursor) {
        match child.kind() {
            "module_definition" => analyze_module_definition(file, module, child, source, analysis),
            "value_definition" => analyze_value_definition(file, module, child, source, analysis),
            _ => {}
        }
    }
}

fn analyze_module_definition(
    file: &Path,
    module: &[String],
    definition: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
) {
    let mut cursor = definition.walk();
    for binding in definition
        .named_children(&mut cursor)
        .filter(|child| child.kind() == "module_binding")
    {
        let Some(name_node) = direct_named_child(binding, "module_name") else {
            continue;
        };
        let Some(body) = binding.child_by_field_name("body") else {
            continue;
        };
        if body.kind() != "structure" {
            continue;
        }

        let mut nested_module = module.to_vec();
        nested_module.push(node_text(name_node, source).to_owned());
        analyze_structure(file, &nested_module, body, source, analysis);
    }
}

fn analyze_value_definition(
    file: &Path,
    module: &[String],
    definition: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
) {
    let mut cursor = definition.walk();
    for binding in definition
        .named_children(&mut cursor)
        .filter(|child| child.kind() == "let_binding")
    {
        if let Some(function) = function_from_binding(file, module, binding, source, analysis) {
            analysis.functions.push(function);
        }
    }
}

fn function_from_binding(
    file: &Path,
    module: &[String],
    binding: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
) -> Option<FunctionInfo> {
    let pattern = binding.child_by_field_name("pattern")?;
    if !matches!(pattern.kind(), "value_name" | "value_pattern") {
        return None;
    }
    let name = node_text(pattern, source).trim();
    if !is_value_identifier(name) {
        return None;
    }

    let binding_body = binding.child_by_field_name("body")?;
    let mut parameters = direct_named_children(binding, "parameter");
    let body = match binding_body.kind() {
        "fun_expression" => {
            parameters.extend(direct_named_children(binding_body, "parameter"));
            binding_body
                .child_by_field_name("body")
                .unwrap_or(binding_body)
        }
        "function_expression" => {
            if parameters.is_empty() {
                parameters.push(binding_body);
            }
            binding_body
        }
        _ if parameters.is_empty() => return None,
        _ => binding_body,
    };

    let id = SymbolId {
        language: LanguageId::new("ocaml"),
        module: module.to_vec(),
        container: None,
        name: name.to_owned(),
    };
    let parameter_labels = parameters
        .iter()
        .map(|parameter| {
            if parameter.kind() == "function_expression" {
                "_".to_owned()
            } else {
                parameter_default_label(*parameter, source)
            }
        })
        .collect::<Vec<_>>();
    let default_label = ocaml_declaration_label(&id, &parameter_labels);
    let typed_label = typed_declaration_label(&id, &parameters, source);

    for (index, parameter) in parameters.iter().enumerate() {
        if parameter.kind() == "function_expression" {
            continue;
        }
        let key = parameter_labels[index].clone();
        let value = parameter_pattern_and_type(*parameter)
            .1
            .map(|node| normalize_source(node_text(node, source)))
            .unwrap_or_default();
        analysis.facts.push(LanguageFact {
            subject: id.clone(),
            namespace: LanguageId::new("ocaml"),
            kind: "parameter".to_owned(),
            key,
            value,
            span: tree_sitter_span(file, *parameter),
        });
    }

    let mut calls = Vec::new();
    collect_calls(file, body, source, true, &mut calls);

    Some(FunctionInfo {
        id,
        label: match typed_label {
            Some(typed) => CallLabel::with_types(default_label, typed),
            None => CallLabel::new(default_label),
        },
        // Without an .mli index, structure bindings are conservatively treated
        // as exported entry candidates. Explicit --entry remains exact.
        public: true,
        calls,
        span: tree_sitter_span(file, binding),
    })
}

fn collect_calls(
    file: &Path,
    node: Node<'_>,
    source: &str,
    is_callable_body: bool,
    calls: &mut Vec<CallSite>,
) {
    if node.kind() == "application_expression" {
        if let Some(function) = node.child_by_field_name("function")
            && let Some(parts) = ocaml_value_path(function, source)
        {
            calls.push(CallSite {
                syntax: CallSyntax::Path(parts),
                target: CallTarget::Unresolved,
                label: CallLabel::new(normalize_source(node_text(node, source))),
                span: tree_sitter_span(file, node),
            });
        }
    } else if !is_callable_body && matches!(node.kind(), "fun_expression" | "function_expression") {
        // A nested closure owns its calls. It will receive its own callable ID
        // when local callable extraction is added.
        return;
    } else if node.kind() == "let_binding" && !direct_named_children(node, "parameter").is_empty() {
        // Likewise, do not attribute a local function's body to its enclosing
        // function.
        return;
    }

    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_calls(file, child, source, false, calls);
    }
}

fn ocaml_value_path(function: Node<'_>, source: &str) -> Option<Vec<String>> {
    if !matches!(
        function.kind(),
        "value_path" | "value_name" | "parenthesized_operator"
    ) {
        return None;
    }
    let raw = normalize_source(node_text(function, source));
    let parts = raw
        .split('.')
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    (!parts.is_empty()).then_some(parts)
}

fn direct_named_child<'tree>(node: Node<'tree>, kind: &str) -> Option<Node<'tree>> {
    let mut cursor = node.walk();
    node.named_children(&mut cursor)
        .find(|child| child.kind() == kind)
}

fn direct_named_children<'tree>(node: Node<'tree>, kind: &str) -> Vec<Node<'tree>> {
    let mut cursor = node.walk();
    node.named_children(&mut cursor)
        .filter(|child| child.kind() == kind)
        .collect()
}

fn node_text<'a>(node: Node<'_>, source: &'a str) -> &'a str {
    node.utf8_text(source.as_bytes())
        .expect("tree-sitter nodes always point into the parsed UTF-8 source")
}

fn ocaml_declaration_label(id: &SymbolId, parameters: &[String]) -> String {
    let name = id
        .module
        .iter()
        .chain(std::iter::once(&id.name))
        .cloned()
        .collect::<Vec<_>>()
        .join(".");
    if parameters.is_empty() {
        name
    } else {
        format!("{name} {}", parameters.join(" "))
    }
}

fn typed_declaration_label(id: &SymbolId, parameters: &[Node<'_>], source: &str) -> Option<String> {
    let mut found_type = false;
    let labels = parameters
        .iter()
        .map(|parameter| {
            if parameter.kind() == "function_expression" {
                return "_".to_owned();
            }
            let (label, typed) = parameter_typed_label(*parameter, source);
            found_type |= typed;
            label
        })
        .collect::<Vec<_>>();
    found_type.then(|| ocaml_declaration_label(id, &labels))
}

fn parameter_default_label(parameter: Node<'_>, source: &str) -> String {
    let (pattern_node, ty) = parameter_pattern_and_type(parameter);
    if ty.is_none() {
        return normalize_source(node_text(parameter, source));
    }

    let pattern = pattern_node
        .map(|pattern| normalize_source(node_text(pattern, source)))
        .unwrap_or_else(|| "_".to_owned());
    let Some(label) = direct_named_child(parameter, "label_name") else {
        return pattern;
    };
    let marker = node_text(parameter, source)
        .trim_start()
        .chars()
        .next()
        .filter(|marker| matches!(marker, '~' | '?'))
        .unwrap_or('~');
    let label = normalize_source(node_text(label, source));
    if pattern == label {
        format!("{marker}{label}")
    } else {
        format!("{marker}{label}:{pattern}")
    }
}

fn parameter_typed_label(parameter: Node<'_>, source: &str) -> (String, bool) {
    let (pattern_node, ty) = parameter_pattern_and_type(parameter);
    let Some(ty) = ty else {
        return (parameter_default_label(parameter, source), false);
    };
    let pattern = pattern_node
        .map(|pattern| normalize_source(node_text(pattern, source)))
        .unwrap_or_else(|| "_".to_owned());
    let annotated = format!("({pattern} : {})", normalize_source(node_text(ty, source)));
    let Some(label) = direct_named_child(parameter, "label_name") else {
        return (annotated, true);
    };
    let marker = node_text(parameter, source)
        .trim_start()
        .chars()
        .next()
        .filter(|marker| matches!(marker, '~' | '?'))
        .unwrap_or('~');
    (
        format!(
            "{marker}{}:{annotated}",
            normalize_source(node_text(label, source))
        ),
        true,
    )
}

fn parameter_pattern_and_type<'tree>(
    parameter: Node<'tree>,
) -> (Option<Node<'tree>>, Option<Node<'tree>>) {
    let pattern = parameter.child_by_field_name("pattern");
    match pattern {
        Some(pattern) if pattern.kind() == "typed_pattern" => (
            pattern.child_by_field_name("pattern"),
            pattern.child_by_field_name("type"),
        ),
        pattern => (pattern, parameter.child_by_field_name("type")),
    }
}

fn is_value_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    chars
        .next()
        .is_some_and(|first| first == '_' || first.is_ascii_lowercase())
        && chars.all(|character| {
            character == '_' || character == '\'' || character.is_ascii_alphanumeric()
        })
}

fn tree_sitter_span(file: &Path, node: Node<'_>) -> SourceSpan {
    SourceSpan {
        file: file.to_path_buf(),
        start_line: node.start_position().row + 1,
        start_column: node.start_position().column,
        start_byte: Some(node.start_byte()),
        end_line: node.end_position().row + 1,
        end_column: node.end_position().column,
        end_byte: Some(node.end_byte()),
    }
}

fn normalize_source(source: &str) -> String {
    let mut output = String::with_capacity(source.len());
    let mut in_string = false;
    let mut escaped = false;
    let mut pending_space = false;

    for character in source.chars() {
        if in_string {
            output.push(character);
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
            continue;
        }

        if character == '"' {
            if pending_space && !output.is_empty() {
                output.push(' ');
            }
            pending_space = false;
            in_string = true;
            output.push(character);
        } else if character.is_whitespace() {
            pending_space = true;
        } else {
            if pending_space && !output.is_empty() {
                output.push(' ');
            }
            pending_space = false;
            output.push(character);
        }
    }
    output.trim().to_owned()
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    #[test]
    fn extracts_module_functions_and_native_call_labels() {
        let source = include_str!("../../examples/ocaml/after.ml");
        let analysis = OcamlFrontend
            .analyze_file(
                &FileContext {
                    path: Path::new("after.ml"),
                    module: &[],
                },
                source,
            )
            .unwrap();

        let save = analysis
            .functions
            .iter()
            .find(|function| function.id.module == ["Postgres"] && function.id.name == "save")
            .unwrap();
        assert_eq!(save.label.default, "Postgres.save order");
        assert_eq!(
            save.calls
                .iter()
                .map(|call| call.label.default.as_str())
                .collect::<Vec<_>>(),
            ["Sql.begin_tx order", "Sql.insert order", "Sql.commit order"]
        );
    }

    #[test]
    fn keeps_labeled_optional_and_unit_application_syntax() {
        let source = r#"
            let run order =
              charge ~currency:"KRW" order 100;
              find ?limit:None ~tenant:"acme" order;
              commit ()
        "#;
        let analysis = OcamlFrontend
            .analyze_file(
                &FileContext {
                    path: Path::new("calls.ml"),
                    module: &[],
                },
                source,
            )
            .unwrap();
        let calls = &analysis.functions[0].calls;
        assert_eq!(calls[0].label.default, "charge ~currency:\"KRW\" order 100");
        assert_eq!(
            calls[1].label.default,
            "find ?limit:None ~tenant:\"acme\" order"
        );
        assert_eq!(calls[2].label.default, "commit ()");
    }

    #[test]
    fn separates_ocaml_parameter_types_from_the_default_label() {
        let source = "let run (order : Order.t) = validate order";
        let analysis = OcamlFrontend
            .analyze_file(
                &FileContext {
                    path: Path::new("typed.ml"),
                    module: &[],
                },
                source,
            )
            .unwrap();
        let label = &analysis.functions[0].label;
        assert_eq!(label.default, "run order");
        assert_eq!(label.typed.as_deref(), Some("run (order : Order.t)"));
    }
}
