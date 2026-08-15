use crate::model::{CallLabel, CallNode, CallRelation, CallSiteId};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DiffStatus {
    Same,
    Added,
    Removed,
    Modified,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiffNode {
    pub key: String,
    pub callsite: Option<CallSiteId>,
    pub label: CallLabel,
    pub relation: CallRelation,
    pub before_label: Option<CallLabel>,
    pub before_relation: Option<CallRelation>,
    pub status: DiffStatus,
    pub children: Vec<DiffNode>,
}

pub fn diff_optional(before: Option<&CallNode>, after: Option<&CallNode>) -> Option<DiffNode> {
    match (before, after) {
        (Some(before), Some(after)) => Some(diff_node(Some(before), Some(after))),
        (Some(before), None) => Some(diff_node(Some(before), None)),
        (None, Some(after)) => Some(diff_node(None, Some(after))),
        (None, None) => None,
    }
}

fn diff_node(before: Option<&CallNode>, after: Option<&CallNode>) -> DiffNode {
    match (before, after) {
        (Some(before), Some(after)) => DiffNode {
            key: after.key.clone(),
            callsite: after.callsite.clone(),
            label: after.label.clone(),
            relation: after.relation,
            before_label: (!labels_equivalent(&before.label.default, &after.label.default)
                || before.relation != after.relation)
                .then(|| before.label.clone()),
            before_relation: (before.relation != after.relation).then_some(before.relation),
            status: if labels_equivalent(&before.label.default, &after.label.default)
                && before.relation == after.relation
            {
                DiffStatus::Same
            } else {
                DiffStatus::Modified
            },
            children: diff_children(&before.children, &after.children),
        },
        (None, Some(after)) => mark_tree(after, DiffStatus::Added),
        (Some(before), None) => mark_tree(before, DiffStatus::Removed),
        (None, None) => unreachable!("diff_node requires at least one node"),
    }
}

fn mark_tree(node: &CallNode, status: DiffStatus) -> DiffNode {
    DiffNode {
        key: node.key.clone(),
        callsite: node.callsite.clone(),
        label: node.label.clone(),
        relation: node.relation,
        before_label: None,
        before_relation: None,
        status,
        children: node
            .children
            .iter()
            .map(|child| mark_tree(child, status))
            .collect(),
    }
}

fn diff_children(before: &[CallNode], after: &[CallNode]) -> Vec<DiffNode> {
    let n = before.len();
    let m = after.len();
    if n == m
        && before
            .iter()
            .zip(after)
            .all(|(before, after)| nodes_equivalent(before, after))
    {
        return before
            .iter()
            .zip(after)
            .map(|(before, after)| diff_node(Some(before), Some(after)))
            .collect();
    }
    let mut score = vec![vec![0usize; m + 1]; n + 1];

    for i in (0..n).rev() {
        for j in (0..m).rev() {
            let matched = alignment_weight(&before[i], &after[j])
                .map(|weight| score[i + 1][j + 1] + weight)
                .unwrap_or_default();
            score[i][j] = matched.max(score[i + 1][j]).max(score[i][j + 1]);
        }
    }

    let mut result = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < n && j < m {
        let matched =
            alignment_weight(&before[i], &after[j]).map(|weight| score[i + 1][j + 1] + weight);
        if matched == Some(score[i][j]) {
            result.push(diff_node(Some(&before[i]), Some(&after[j])));
            i += 1;
            j += 1;
        } else if score[i + 1][j] >= score[i][j + 1] {
            result.push(diff_node(Some(&before[i]), None));
            i += 1;
        } else {
            result.push(diff_node(None, Some(&after[j])));
            j += 1;
        }
    }
    while i < n {
        result.push(diff_node(Some(&before[i]), None));
        i += 1;
    }
    while j < m {
        result.push(diff_node(None, Some(&after[j])));
        j += 1;
    }
    result
}

fn nodes_equivalent(before: &CallNode, after: &CallNode) -> bool {
    semantic_keys_equivalent(&before.key, &after.key)
        && labels_equivalent(&before.label.default, &after.label.default)
        && before.relation == after.relation
        && before.children.len() == after.children.len()
        && before
            .children
            .iter()
            .zip(&after.children)
            .all(|(before, after)| nodes_equivalent(before, after))
}

/// Prefer unchanged source labels and shallow call shape while still allowing
/// a modified call to align by semantic target. `CallSiteId` currently embeds
/// absolute source coordinates, so it must not influence cross-revision
/// alignment: inserting a line can otherwise pair every repeated call with the
/// following occurrence.
fn alignment_weight(before: &CallNode, after: &CallNode) -> Option<usize> {
    if !semantic_keys_equivalent(&before.key, &after.key) {
        return None;
    }
    let mut weight = 10usize;
    if before.label.default == after.label.default && !before.label.default.contains("λ#") {
        weight += 100;
    } else if labels_equivalent(&before.label.default, &after.label.default) {
        weight += 80;
    }
    if before.relation == after.relation {
        weight += 5;
    }
    if same_shallow_children(before, after) {
        weight += 25;
    }
    weight += matching_descendant_weight(before, after, 2).min(100);
    Some(weight)
}

fn semantic_keys_equivalent(before: &str, after: &str) -> bool {
    before == after
        || normalize_anonymous_lambda_keys(before) == normalize_anonymous_lambda_keys(after)
}

fn normalize_anonymous_lambda_keys(key: &str) -> String {
    let mut normalized = String::with_capacity(key.len());
    let mut remainder = key;
    while let Some(start) = remainder.find("{lambda:") {
        normalized.push_str(&remainder[..start]);
        normalized.push_str("{lambda}");
        let located = &remainder[start..];
        let Some(end) = located.find('}') else {
            normalized.push_str(located);
            return normalized;
        };
        remainder = &located[end + 1..];
    }
    normalized.push_str(remainder);
    normalized
}

fn labels_equivalent(before: &str, after: &str) -> bool {
    before == after || normalize_anonymous_lambdas(before) == normalize_anonymous_lambdas(after)
}

fn normalize_anonymous_lambdas(label: &str) -> String {
    let mut normalized = String::with_capacity(label.len());
    let mut rest = label;
    while let Some(index) = rest.find("λ#") {
        normalized.push_str(&rest[..index + "λ#".len()]);
        rest = &rest[index + "λ#".len()..];
        let digits = rest.chars().take_while(char::is_ascii_digit).count();
        rest = &rest[digits..];
    }
    normalized.push_str(rest);
    normalized
}

fn same_shallow_children(before: &CallNode, after: &CallNode) -> bool {
    before.children.len() == after.children.len()
        && before
            .children
            .iter()
            .zip(&after.children)
            .all(|(before, after)| {
                semantic_keys_equivalent(&before.key, &after.key)
                    && labels_equivalent(&before.label.default, &after.label.default)
            })
}

fn matching_descendant_weight(before: &CallNode, after: &CallNode, depth: usize) -> usize {
    if depth == 0 || before.children.len() != after.children.len() {
        return 0;
    }
    before
        .children
        .iter()
        .zip(&after.children)
        .map(|(before, after)| {
            if !semantic_keys_equivalent(&before.key, &after.key) {
                return 0;
            }
            10 + usize::from(labels_equivalent(
                &before.label.default,
                &after.label.default,
            )) * 10
                + matching_descendant_weight(before, after, depth - 1)
        })
        .sum()
}

/// Apply the presentation depth after the complete trees have been compared.
/// A hidden changed path is represented explicitly instead of being mistaken
/// for "no call changes".
pub fn truncate_diff_tree(node: &mut DiffNode, max_depth: usize) {
    truncate_diff_tree_at(node, max_depth, 0);
}

fn truncate_diff_tree_at(node: &mut DiffNode, max_depth: usize, depth: usize) {
    if depth >= max_depth {
        if node.children.iter().any(tree_has_changes) {
            node.children = vec![DiffNode {
                key: format!("{}#depth-limit", node.key),
                callsite: None,
                label: CallLabel::new("… changed below max depth"),
                relation: CallRelation::Call,
                before_label: None,
                before_relation: None,
                status: DiffStatus::Added,
                children: Vec::new(),
            }];
        } else {
            node.children.clear();
        }
        return;
    }
    for child in &mut node.children {
        truncate_diff_tree_at(child, max_depth, depth + 1);
    }
}

pub fn tree_has_changes(node: &DiffNode) -> bool {
    node.status != DiffStatus::Same || node.children.iter().any(tree_has_changes)
}

/// Keep unchanged siblings as one-line context while hiding their unchanged
/// descendants. Paths that lead to a change and fully added/removed subtrees
/// remain expanded.
pub fn collapse_unchanged_subtrees(node: &mut DiffNode) -> bool {
    let carries_dispatch_context = subtree_has_dispatch_context(node);
    let mut descendants_changed = false;
    for child in &mut node.children {
        descendants_changed |= collapse_unchanged_subtrees(child);
    }
    let changed = node.status != DiffStatus::Same || descendants_changed;
    if !changed && !carries_dispatch_context {
        node.children.clear();
    }
    changed
}

fn subtree_has_dispatch_context(node: &DiffNode) -> bool {
    node.relation == CallRelation::DispatchCandidate
        || node.children.iter().any(subtree_has_dispatch_context)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{CallLabel, CallSiteId};

    fn node(key: &str, label: CallLabel, children: Vec<CallNode>) -> CallNode {
        CallNode {
            key: key.to_owned(),
            callsite: None,
            label,
            relation: CallRelation::Call,
            children,
        }
    }

    fn call(key: &str, site: &str, label: &str) -> CallNode {
        CallNode {
            key: key.to_owned(),
            callsite: Some(CallSiteId(site.to_owned())),
            label: CallLabel::new(label),
            relation: CallRelation::Call,
            children: Vec::new(),
        }
    }

    #[test]
    fn aligns_by_semantic_key_and_records_a_display_change() {
        let before = node("rust://save", CallLabel::new("save(order)"), Vec::new());
        let after = node(
            "rust://save",
            CallLabel::new("save(next_order)"),
            Vec::new(),
        );

        let diff = diff_optional(Some(&before), Some(&after)).unwrap();
        assert_eq!(diff.key, "rust://save");
        assert_eq!(diff.status, DiffStatus::Modified);
        assert_eq!(
            diff.before_label
                .as_ref()
                .map(|label| label.default.as_str()),
            Some("save(order)")
        );
    }

    #[test]
    fn typed_labels_do_not_create_noise_in_the_default_call_diff() {
        let before = node(
            "rust://save",
            CallLabel::with_types("save(order)", "save(order: OldOrder)"),
            Vec::new(),
        );
        let after = node(
            "rust://save",
            CallLabel::with_types("save(order)", "save(order: NewOrder)"),
            Vec::new(),
        );

        let diff = diff_optional(Some(&before), Some(&after)).unwrap();
        assert_eq!(diff.status, DiffStatus::Same);
        assert!(!tree_has_changes(&diff));
    }

    #[test]
    fn collapses_unchanged_context_below_its_first_line() {
        let stable = node(
            "rust://stable",
            CallLabel::new("stable()"),
            vec![node("rust://deep", CallLabel::new("deep()"), Vec::new())],
        );
        let before = node(
            "rust://root",
            CallLabel::new("root()"),
            vec![
                stable.clone(),
                node("rust://old", CallLabel::new("old()"), Vec::new()),
            ],
        );
        let after = node(
            "rust://root",
            CallLabel::new("root()"),
            vec![
                stable,
                node("rust://new", CallLabel::new("new()"), Vec::new()),
            ],
        );
        let mut diff = diff_optional(Some(&before), Some(&after)).unwrap();

        assert!(collapse_unchanged_subtrees(&mut diff));
        assert_eq!(diff.children[0].label.default, "stable()");
        assert!(diff.children[0].children.is_empty());
    }

    #[test]
    fn aligns_repeated_callees_by_callsite_and_label_before_target_fallback() {
        let before = node(
            "rust://root",
            CallLabel::new("root()"),
            vec![
                call("rust://save", "save@1", "save(first)"),
                call("rust://save", "save@2", "save(second)"),
            ],
        );
        let after = node(
            "rust://root",
            CallLabel::new("root()"),
            vec![
                call("rust://save", "save@0", "save(inserted)"),
                call("rust://save", "save@1", "save(first)"),
                call("rust://save", "save@2", "save(second)"),
            ],
        );

        let diff = diff_optional(Some(&before), Some(&after)).unwrap();
        assert_eq!(
            diff.children
                .iter()
                .map(|node| (node.label.default.as_str(), node.status))
                .collect::<Vec<_>>(),
            vec![
                ("save(inserted)", DiffStatus::Added),
                ("save(first)", DiffStatus::Same),
                ("save(second)", DiffStatus::Same),
            ]
        );
    }

    #[test]
    fn absolute_source_line_shifts_do_not_corrupt_repeated_call_alignment() {
        let before = node(
            "rust://root",
            CallLabel::new("root()"),
            vec![
                call("rust://touch", "touch@4", "touch(item)"),
                call("rust://touch", "touch@5", "touch(item)"),
                call("rust://touch", "touch@6", "touch(item)"),
            ],
        );
        let after = node(
            "rust://root",
            CallLabel::new("root()"),
            vec![
                call("rust://touch", "touch@5", "touch(item)"),
                call("rust://touch", "touch@6", "touch(item)"),
                call("rust://touch", "touch@7", "touch(item)"),
                call("rust://finish", "finish@8", "finish()"),
            ],
        );

        let diff = diff_optional(Some(&before), Some(&after)).unwrap();
        assert_eq!(diff.children.len(), 4);
        assert!(
            diff.children[..3]
                .iter()
                .all(|node| node.status == DiffStatus::Same)
        );
        assert_eq!(diff.children[3].label.default, "finish()");
        assert_eq!(diff.children[3].status, DiffStatus::Added);
    }

    #[test]
    fn preserves_a_deep_change_when_presentation_depth_is_small() {
        let before = node(
            "root",
            CallLabel::new("root()"),
            vec![node(
                "a",
                CallLabel::new("a()"),
                vec![node("b", CallLabel::new("b()"), Vec::new())],
            )],
        );
        let after = node(
            "root",
            CallLabel::new("root()"),
            vec![node(
                "a",
                CallLabel::new("a()"),
                vec![node(
                    "b",
                    CallLabel::new("b()"),
                    vec![node("new", CallLabel::new("new()"), Vec::new())],
                )],
            )],
        );
        let mut diff = diff_optional(Some(&before), Some(&after)).unwrap();
        assert!(tree_has_changes(&diff));
        truncate_diff_tree(&mut diff, 1);
        assert_eq!(
            diff.children[0].children[0].label.default,
            "… changed below max depth"
        );
    }
}
