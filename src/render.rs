use crate::diff::{DiffNode, DiffStatus};
use crate::engine::{DiffReport, TreeReport};
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

pub fn render_tree_report_with_options(report: &TreeReport, options: &RenderOptions) -> String {
    let mut parts = vec![report.source.clone(), String::new()];
    if let Some(message) = &report.message {
        parts.push(message.clone());
        return parts.join("\n");
    }
    for (index, entry) in report.trees.iter().enumerate() {
        if index > 0 {
            parts.push(String::new());
        }
        parts.push(render_call_tree_with_options(&entry.tree, options));
    }
    parts.join("\n")
}

pub fn render_call_tree_with_options(
    root: &crate::model::CallNode,
    options: &RenderOptions,
) -> String {
    let diff = crate::diff::diff_optional(Some(root), Some(root))
        .expect("a call tree always produces a diff node");
    render_diff_tree_with_options(&diff, options)
}

pub fn render_diff_tree(root: &DiffNode) -> String {
    render_diff_tree_with_options(root, &RenderOptions::default())
}

pub fn render_diff_tree_with_options(root: &DiffNode, options: &RenderOptions) -> String {
    let mut lines = Vec::new();
    render_node(root, "", true, true, options, &mut lines);
    connect_back_edges(&mut lines);
    lines
        .into_iter()
        .map(|line| match line.color {
            Some(color) => color_line(line.text, color, options.color),
            None => line.text,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

#[derive(Debug)]
struct RenderLine {
    text: String,
    color: Option<AnsiColor>,
    key: Option<String>,
    backedge_target: Option<String>,
}

fn render_node(
    node: &DiffNode,
    indent: &str,
    is_last: bool,
    is_root: bool,
    options: &RenderOptions,
    lines: &mut Vec<RenderLine>,
) {
    let branch_prefix = branch(node.relation, is_last, is_root);
    if node.relation == CallRelation::BackEdge {
        let (marker, color) = match node.status {
            DiffStatus::Same => ("  ", None),
            DiffStatus::Added => ("+ ", Some(AnsiColor::Green)),
            DiffStatus::Removed => ("- ", Some(AnsiColor::Red)),
            DiffStatus::Modified => ("+ ", Some(AnsiColor::Green)),
        };
        lines.push(RenderLine {
            text: format!(
                "{marker}{indent}{branch_prefix}{}",
                node.label.text(options.show_types)
            ),
            color,
            key: None,
            backedge_target: Some(node.key.clone()),
        });
        return;
    }

    match node.status {
        DiffStatus::Same => lines.push(RenderLine {
            text: format!(
                "  {indent}{branch_prefix}{}",
                node.label.text(options.show_types)
            ),
            color: None,
            key: backedge_anchor(node),
            backedge_target: None,
        }),
        DiffStatus::Added => lines.push(RenderLine {
            text: format!(
                "+ {indent}{branch_prefix}{}",
                node.label.text(options.show_types)
            ),
            color: Some(AnsiColor::Green),
            key: backedge_anchor(node),
            backedge_target: None,
        }),
        DiffStatus::Removed => lines.push(RenderLine {
            text: format!(
                "- {indent}{branch_prefix}{}",
                node.label.text(options.show_types)
            ),
            color: Some(AnsiColor::Red),
            key: backedge_anchor(node),
            backedge_target: None,
        }),
        DiffStatus::Modified => {
            let before = node
                .before_label
                .as_ref()
                .expect("modified nodes carry their previous label");
            lines.push(RenderLine {
                text: format!(
                    "- {indent}{}{}",
                    branch(
                        node.before_relation.unwrap_or(node.relation),
                        is_last,
                        is_root
                    ),
                    before.text(options.show_types)
                ),
                color: Some(AnsiColor::Red),
                key: backedge_anchor(node),
                backedge_target: None,
            });
            lines.push(RenderLine {
                text: format!(
                    "+ {indent}{branch_prefix}{}",
                    node.label.text(options.show_types)
                ),
                color: Some(AnsiColor::Green),
                key: backedge_anchor(node),
                backedge_target: None,
            });
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
            CallRelation::BackEdge => unreachable!("back edges have no children"),
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

fn backedge_anchor(node: &DiffNode) -> Option<String> {
    (!node.children.is_empty()).then(|| node.key.clone())
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
            (CallRelation::BackEdge, false) => "├─ ",
            (CallRelation::BackEdge, true) => "└─ ",
        }
    }
}

fn connect_back_edges(lines: &mut [RenderLine]) {
    let edges = lines
        .iter()
        .enumerate()
        .filter_map(|(end, line)| {
            let target = line.backedge_target.as_ref()?;
            let start = lines[..end]
                .iter()
                .rposition(|candidate| candidate.key.as_ref() == Some(target))?;
            Some((start, end))
        })
        .collect::<Vec<_>>();
    if edges.is_empty() {
        return;
    }

    let original_lengths = lines
        .iter()
        .map(|line| line.text.trim_end().chars().count())
        .collect::<Vec<_>>();
    let base_rail = original_lengths.iter().copied().max().unwrap_or(0) + 3;
    let mut rows = lines
        .iter()
        .map(|line| line.text.trim_end().chars().collect::<Vec<_>>())
        .collect::<Vec<_>>();

    let mut grouped = std::collections::BTreeMap::<usize, Vec<usize>>::new();
    for (start, end) in edges {
        grouped.entry(start).or_default().push(end);
    }

    for (rail_index, (start, ends)) in grouped.into_iter().enumerate() {
        let rail = base_rail + rail_index * 3;
        let arrow = original_lengths[start] + 1;
        set_glyph(&mut rows[start], arrow, '◀');
        for column in arrow + 1..rail {
            set_glyph(&mut rows[start], column, '─');
        }
        set_glyph(&mut rows[start], rail, '┐');

        let last_end = *ends.last().expect("a back-edge group is never empty");
        for row in rows.iter_mut().take(last_end).skip(start + 1) {
            set_glyph(row, rail, '│');
        }
        for end in ends {
            for column in original_lengths[end] + 1..rail {
                set_glyph(&mut rows[end], column, '─');
            }
            set_glyph(
                &mut rows[end],
                rail,
                if end == last_end { '┘' } else { '┤' },
            );
        }
    }

    for (line, row) in lines.iter_mut().zip(rows) {
        line.text = row.into_iter().collect::<String>().trim_end().to_owned();
    }
}

fn set_glyph(row: &mut Vec<char>, column: usize, glyph: char) {
    if row.len() <= column {
        row.resize(column + 1, ' ');
    }
    row[column] = merge_glyph(row[column], glyph);
}

fn merge_glyph(existing: char, next: char) -> char {
    match (existing, next) {
        (' ', next) => next,
        ('─', '│') | ('│', '─') => '┼',
        (_, next) => next,
    }
}

#[derive(Clone, Copy, Debug)]
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
            callsite: None,
            label: CallLabel::new("run(store, order)"),
            relation: CallRelation::Call,
            children: vec![CallNode {
                key: "rust://Store::save".to_owned(),
                callsite: None,
                label: CallLabel::new("dyn Store::save(order)"),
                relation: CallRelation::Call,
                children: vec![
                    CallNode {
                        key: "rust://Postgres::save".to_owned(),
                        callsite: None,
                        label: CallLabel::new("Postgres::save(order)"),
                        relation: CallRelation::DispatchCandidate,
                        children: vec![CallNode {
                            key: "rust://sql::insert".to_owned(),
                            callsite: None,
                            label: CallLabel::new("sql::insert(order)"),
                            relation: CallRelation::Call,
                            children: Vec::new(),
                        }],
                    },
                    CallNode {
                        key: "rust://S3::save".to_owned(),
                        callsite: None,
                        label: CallLabel::new("S3::save(order)"),
                        relation: CallRelation::DispatchCandidate,
                        children: vec![CallNode {
                            key: "rust://aws::put_object".to_owned(),
                            callsite: None,
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

    #[test]
    fn renders_recursive_calls_as_right_side_back_edges() {
        let tree = CallNode {
            key: "rust://a".to_owned(),
            callsite: None,
            label: CallLabel::new("a()"),
            relation: CallRelation::Call,
            children: vec![CallNode {
                key: "rust://b".to_owned(),
                callsite: None,
                label: CallLabel::new("b()"),
                relation: CallRelation::Call,
                children: vec![CallNode {
                    key: "rust://a".to_owned(),
                    callsite: None,
                    label: CallLabel::new("a()"),
                    relation: CallRelation::BackEdge,
                    children: Vec::new(),
                }],
            }],
        };

        assert_eq!(
            render_call_tree_with_options(
                &tree,
                &RenderOptions {
                    show_types: false,
                    color: ColorMode::Plain,
                },
            ),
            "  a() ◀───────┐\n  └─ b()      │\n     └─ a() ──┘"
        );
    }

    #[test]
    fn shares_one_rail_between_calls_to_the_same_recursive_ancestor() {
        let back_edge = |label: &str| CallNode {
            key: "ocaml://walk".to_owned(),
            callsite: None,
            label: CallLabel::new(label),
            relation: CallRelation::BackEdge,
            children: Vec::new(),
        };
        let tree = CallNode {
            key: "ocaml://walk".to_owned(),
            callsite: None,
            label: CallLabel::new("walk value"),
            relation: CallRelation::Call,
            children: vec![
                back_edge("walk left"),
                back_edge("walk right"),
                back_edge("walk tail"),
            ],
        };

        let rendered = render_call_tree_with_options(
            &tree,
            &RenderOptions {
                show_types: false,
                color: ColorMode::Plain,
            },
        );
        assert_eq!(rendered.matches('┐').count(), 1, "{rendered}");
        assert_eq!(rendered.matches('┤').count(), 2, "{rendered}");
        assert_eq!(rendered.matches('┘').count(), 1, "{rendered}");
        assert!(rendered.lines().all(|line| line.chars().count() < 32));
    }

    #[test]
    fn keeps_partial_and_unresolved_dispatch_wording_distinct() {
        let tree = CallNode {
            key: "rust://run".to_owned(),
            callsite: None,
            label: CallLabel::new("run(store)"),
            relation: CallRelation::Call,
            children: vec![
                CallNode {
                    key: "rust://Store::save#partial".to_owned(),
                    callsite: None,
                    label: CallLabel::new("dyn Store::save() [partial]"),
                    relation: CallRelation::Call,
                    children: vec![
                        CallNode {
                            key: "rust://Postgres::save".to_owned(),
                            callsite: None,
                            label: CallLabel::new("Postgres::save()"),
                            relation: CallRelation::DispatchCandidate,
                            children: Vec::new(),
                        },
                        CallNode {
                            key: "rust://Store::save#unresolved".to_owned(),
                            callsite: None,
                            label: CallLabel::new("… unresolved targets"),
                            relation: CallRelation::DispatchCandidate,
                            children: Vec::new(),
                        },
                    ],
                },
                CallNode {
                    key: "rust://Store::load".to_owned(),
                    callsite: None,
                    label: CallLabel::new("dyn Store::load() [unresolved]"),
                    relation: CallRelation::Call,
                    children: Vec::new(),
                },
            ],
        };

        assert_eq!(
            render_call_tree_with_options(
                &tree,
                &RenderOptions {
                    show_types: false,
                    color: ColorMode::Plain,
                },
            ),
            "  run(store)\n  ├─ dyn Store::save() [partial]\n  │  ╠═ Postgres::save()\n  │  ╚═ … unresolved targets\n  └─ dyn Store::load() [unresolved]"
        );
    }
}
