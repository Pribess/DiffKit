use crate::model::{CallLabel, CallNode, CallRelation};

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
            label: after.label.clone(),
            relation: after.relation,
            before_label: (before.label.default != after.label.default
                || before.relation != after.relation)
                .then(|| before.label.clone()),
            before_relation: (before.relation != after.relation).then_some(before.relation),
            status: if before.label.default == after.label.default
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
    let mut lcs = vec![vec![0usize; m + 1]; n + 1];

    for i in (0..n).rev() {
        for j in (0..m).rev() {
            lcs[i][j] = if before[i].key == after[j].key {
                lcs[i + 1][j + 1] + 1
            } else {
                lcs[i + 1][j].max(lcs[i][j + 1])
            };
        }
    }

    let mut result = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < n && j < m {
        if before[i].key == after[j].key {
            result.push(diff_node(Some(&before[i]), Some(&after[j])));
            i += 1;
            j += 1;
        } else if lcs[i + 1][j] >= lcs[i][j + 1] {
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

pub fn tree_has_changes(node: &DiffNode) -> bool {
    node.status != DiffStatus::Same || node.children.iter().any(tree_has_changes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::CallLabel;

    fn node(key: &str, label: CallLabel, children: Vec<CallNode>) -> CallNode {
        CallNode {
            key: key.to_owned(),
            label,
            relation: CallRelation::Call,
            children,
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
}
