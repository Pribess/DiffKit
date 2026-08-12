use crate::diff::{DiffNode, DiffStatus};
use crate::engine::DiffReport;

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
    let branch = if is_root {
        ""
    } else if is_last {
        "└─ "
    } else {
        "├─ "
    };
    match node.status {
        DiffStatus::Same => lines.push(format!(
            "  {indent}{branch}{}",
            node.label.text(options.show_types)
        )),
        DiffStatus::Added => lines.push(color_line(
            format!("+ {indent}{branch}{}", node.label.text(options.show_types)),
            AnsiColor::Green,
            options.color,
        )),
        DiffStatus::Removed => lines.push(color_line(
            format!("- {indent}{branch}{}", node.label.text(options.show_types)),
            AnsiColor::Red,
            options.color,
        )),
        DiffStatus::Modified => {
            let before = node
                .before_label
                .as_ref()
                .expect("modified nodes carry their previous label");
            lines.push(color_line(
                format!("- {indent}{branch}{}", before.text(options.show_types)),
                AnsiColor::Red,
                options.color,
            ));
            lines.push(color_line(
                format!("+ {indent}{branch}{}", node.label.text(options.show_types)),
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
        format!("{indent}│  ")
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
}
