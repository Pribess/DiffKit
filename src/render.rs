use crate::diff::{DiffNode, DiffStatus};
use crate::engine::DiffReport;
use crate::model::CallRelation;

pub fn render_report(report: &DiffReport) -> String {
    render_report_with_options(report, &RenderOptions::default())
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ColorMode {
    #[default]
    Ansi,
    Plain,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RenderOptions {
    pub show_types: bool,
    pub color: ColorMode,
}

pub fn render_report_with_options(report: &DiffReport, options: &RenderOptions) -> String {
    let mut parts = vec![
        format!(
            "{}diff {} → {}",
            report.language, report.before, report.after
        ),
        String::new(),
    ];

    if let Some(message) = &report.message {
        parts.push(message.clone());
        return parts.join("\n");
    }

    for (index, entry) in report.trees.iter().enumerate() {
        if index > 0 {
            parts.push(String::new());
        }
        parts.push(render_diff_tree_with_options(&entry.tree, options));
    }
    parts.join("\n")
}

pub fn render_diff_tree(root: &DiffNode) -> String {
    render_diff_tree_with_options(root, &RenderOptions::default())
}

pub fn render_diff_tree_with_options(root: &DiffNode, options: &RenderOptions) -> String {
    let mut lines = Vec::new();
    render_node(root, "", true, true, options, &mut lines);
    lines.join("\n")
}

fn render_node(
    node: &DiffNode,
    indent: &str,
    is_last: bool,
    is_root: bool,
    options: &RenderOptions,
    lines: &mut Vec<String>,
) {
    let branch_prefix = branch(node.relation, is_last, is_root);
    match node.status {
        DiffStatus::Same => lines.push(format!(
            "  {indent}{branch_prefix}{}",
            node.label.text(options.show_types)
        )),
        DiffStatus::Added => lines.push(color_line(
            format!(
                "+ {indent}{branch_prefix}{}",
                node.label.text(options.show_types)
            ),
            AnsiColor::Green,
            options.color,
        )),
        DiffStatus::Removed => lines.push(color_line(
            format!(
                "- {indent}{branch_prefix}{}",
                node.label.text(options.show_types)
            ),
            AnsiColor::Red,
            options.color,
        )),
        DiffStatus::Modified => {
            let before = node
                .before_label
                .as_ref()
                .expect("modified nodes carry their previous label");
            lines.push(color_line(
                format!(
                    "- {indent}{}{}",
                    branch(
                        node.before_relation.unwrap_or(node.relation),
                        is_last,
                        is_root
                    ),
                    before.text(options.show_types)
                ),
                AnsiColor::Red,
                options.color,
            ));
            lines.push(color_line(
                format!(
                    "+ {indent}{branch_prefix}{}",
                    node.label.text(options.show_types)
                ),
                AnsiColor::Green,
                options.color,
            ));
        }
    }

    let child_indent = if is_root {
        String::new()
    } else if is_last {
        format!("{indent}   ")
    } else {
        let continuation = match node.relation {
            CallRelation::Call => "│  ",
            CallRelation::DispatchCandidate => "║  ",
        };
        format!("{indent}{continuation}")
    };
    for (index, child) in node.children.iter().enumerate() {
        render_node(
            child,
            &child_indent,
            index + 1 == node.children.len(),
            false,
            options,
            lines,
        );
    }
}

fn branch(relation: CallRelation, is_last: bool, is_root: bool) -> &'static str {
    if is_root {
        ""
    } else {
        match (relation, is_last) {
            (CallRelation::Call, false) => "├─ ",
            (CallRelation::Call, true) => "└─ ",
            (CallRelation::DispatchCandidate, false) => "╠═ ",
            (CallRelation::DispatchCandidate, true) => "╚═ ",
        }
    }
}

#[derive(Clone, Copy)]
enum AnsiColor {
    Red,
    Green,
}

fn color_line(line: String, color: AnsiColor, mode: ColorMode) -> String {
    if mode == ColorMode::Plain {
        return line;
    }
    let code = match color {
        AnsiColor::Red => 31,
        AnsiColor::Green => 32,
    };
    format!("\u{1b}[{code}m{line}\u{1b}[0m")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diff::diff_optional;
    use crate::model::{CallLabel, CallNode, CallRelation};

    #[test]
    fn ansi_is_the_default_color_mode() {
        assert_eq!(ColorMode::default(), ColorMode::Ansi);
        assert_eq!(RenderOptions::default().color, ColorMode::Ansi);
    }

    #[test]
    fn ansi_mode_colors_complete_diff_lines() {
        assert_eq!(
            color_line(
                "+ └─ commit()".to_owned(),
                AnsiColor::Green,
                ColorMode::Ansi
            ),
            "\u{1b}[32m+ └─ commit()\u{1b}[0m"
        );
        assert_eq!(
            color_line(
                "- └─ rollback()".to_owned(),
                AnsiColor::Red,
                ColorMode::Ansi
            ),
            "\u{1b}[31m- └─ rollback()\u{1b}[0m"
        );
    }

    #[test]
    fn plain_mode_has_no_terminal_control_sequences() {
        assert_eq!(
            color_line(
                "+ └─ commit()".to_owned(),
                AnsiColor::Green,
                ColorMode::Plain
            ),
            "+ └─ commit()"
        );
    }

    #[test]
    fn renders_dispatch_candidates_with_a_complete_double_line_relation() {
        let tree = CallNode {
            key: "rust://run".to_owned(),
            label: CallLabel::new("run(store, order)"),
            relation: CallRelation::Call,
            children: vec![CallNode {
                key: "rust://Store::save".to_owned(),
                label: CallLabel::new("dyn Store::save(order)"),
                relation: CallRelation::Call,
                children: vec![
                    CallNode {
                        key: "rust://Postgres::save".to_owned(),
                        label: CallLabel::new("Postgres::save(order)"),
                        relation: CallRelation::DispatchCandidate,
                        children: vec![CallNode {
                            key: "rust://sql::insert".to_owned(),
                            label: CallLabel::new("sql::insert(order)"),
                            relation: CallRelation::Call,
                            children: Vec::new(),
                        }],
                    },
                    CallNode {
                        key: "rust://S3::save".to_owned(),
                        label: CallLabel::new("S3::save(order)"),
                        relation: CallRelation::DispatchCandidate,
                        children: vec![CallNode {
                            key: "rust://aws::put_object".to_owned(),
                            label: CallLabel::new("aws::put_object(order)"),
                            relation: CallRelation::Call,
                            children: Vec::new(),
                        }],
                    },
                ],
            }],
        };
        let diff = diff_optional(Some(&tree), Some(&tree)).unwrap();

        assert_eq!(
            render_diff_tree_with_options(
                &diff,
                &RenderOptions {
                    show_types: false,
                    color: ColorMode::Plain,
                },
            ),
            "  run(store, order)\n  └─ dyn Store::save(order)\n     ╠═ Postgres::save(order)\n     ║  └─ sql::insert(order)\n     ╚═ S3::save(order)\n        └─ aws::put_object(order)"
        );
    }
}
