#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_public;

pub mod diff;
pub mod engine;
pub mod git;
pub mod graph;
pub mod language;
pub mod model;
pub mod render;

pub type DiffkitResult<T> = std::result::Result<T, Box<dyn std::error::Error + Send + Sync>>;

pub use engine::{
    DiffOptions, DiffReport, EntryTree, TreeReport, ocamldiff_paths, ocamldiff_project_files,
    ocamldiff_sources, ocamltree_path, ocamltree_project_file, rustdiff_paths,
    rustdiff_project_files, rustdiff_project_paths, rustdiff_project_paths_cached,
    rustdiff_sources, rusttree_path, rusttree_project_file,
};
pub use render::{
    ColorMode, RenderOptions, render_call_tree_with_options, render_report,
    render_report_with_options, render_tree_report_with_options,
};
