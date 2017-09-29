use getopts;
use rustc::session::Session;
use rustc::middle::cstore::CrateStore;
use rustc_driver::{self, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_driver::driver::{CompileState, CompileController};
use rustc::session::config::{self, Input, ErrorOutputType};
use rustc::hir::{self, itemlikevisit, Item_, VariantData, QPath};
use rustc::hir::intravisit::Visitor;
use rustc::ty::TyCtxt;
use rustc_errors;
use syntax::ast as s_ast;
use syntax_pos::Span;

use ast;
use lalrpop_intern::intern;
use std::default::Default;
use std::cell::Cell;
use std::path::PathBuf;
use errors::Result;

thread_local! {
    static PROG_STORE: Cell<Vec<ast::Item>> = Cell::new(Default::default());
}

fn add_prog_item(item: ast::Item) {
    PROG_STORE.with(|prog| {
        let mut p = prog.take();
        p.push(item);
        prog.set(p);
    })
}

fn get_prog() -> Vec<ast::Item> {
    PROG_STORE.with(|prog| prog.take())
}

struct ParseCompilerCalls{default: RustcDefaultCalls}

impl<'a> CompilerCalls<'a> for ParseCompilerCalls {
    fn early_callback(
        &mut self,
        matches: &getopts::Matches,
        sopts: &config::Options,
        cfg: &s_ast::CrateConfig,
        descriptions: &rustc_errors::registry::Registry,
        output: ErrorOutputType,
    ) -> Compilation {
        self.default.early_callback(
            matches,
            sopts,
            cfg,
            descriptions,
            output,
        )
    }
    fn no_input(
        &mut self,
        matches: &getopts::Matches,
        sopts: &config::Options,
        cfg: &s_ast::CrateConfig,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>,
        descriptions: &rustc_errors::registry::Registry,
    ) -> Option<(Input, Option<PathBuf>)> {
        self.default.no_input(
            matches,
            sopts,
            cfg,
            odir,
            ofile,
            descriptions,
        )
    }
    fn late_callback(
        &mut self,
        matches: &getopts::Matches,
        sess: &Session,
        cstore: &CrateStore,
        input: &Input,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>,
    ) -> Compilation {
        self.default.late_callback(matches, sess, cstore, input, odir, ofile)
    }
    fn build_controller(
        &mut self,
        sess: &Session,
        matches: &getopts::Matches,
    ) -> CompileController<'a> {
        let mut control = self.default.build_controller(sess, matches);
        control.after_analysis.callback = Box::new(after_analysis);
        control.after_analysis.stop = Compilation::Stop;
        control
    }
}

impl From<Span> for ast::Span {
    fn from(s: Span) -> Self {
        ast::Span{
            lo: s.lo.0 as usize,
            hi: s.hi.0 as usize,
        }
    }
}

impl<'a> From<&'a hir::Item> for ast::Identifier {
    fn from(i: &'a hir::Item) -> Self {
        ast::Identifier{
            str: intern(&i.name.as_str()),
            span: ast::Span::from(i.span),
        }
    }
}

impl<'a> From<&'a hir::StructField> for ast::Identifier {
    fn from(i: &'a hir::StructField) -> Self {
        ast::Identifier{
            str: intern(&i.name.as_str()),
            span: ast::Span::from(i.span),
        }
    }
}

impl<'a> From<&'a hir::StructField> for ast::Field {
    fn from(f: &'a hir::StructField) -> Self {
        ast::Field{
            name:ast::Identifier::from(f),
            ty:ast::Ty::from(&*f.ty),
        }
    }
}

// define some filler type for unused
// or unimplemented types of rustc
const UKT: &str = "UnknownType";
fn unknown_type() -> ast::Ty {
    let zerospan = ast::Span{lo:0,hi:0};
    ast::Ty::Id{name:ast::Identifier{
        str: intern(UKT),
        span: zerospan,
    }}
}
fn unknown_type_item() -> ast::Item {
    let zerospan = ast::Span{lo:0,hi:0};
    ast::Item::StructDefn(ast::StructDefn{
        name: ast::Identifier{
            str: intern(UKT),
            span: zerospan,
        },
        fields:Vec::new(),
        parameter_kinds:Vec::new(),
        where_clauses:Vec::new(),
    })
}

impl<'a> From<&'a hir::Ty> for ast::Ty {
    fn from(t: &'a hir::Ty) -> Self {
        let span = ast::Span::from(t.span);
        match t.node {
            // TODO: get real types
            hir::Ty_::TyPath(QPath::Resolved(ref s, ref path)) => {
                unknown_type()
            },
            hir::Ty_::TyPath(QPath::TypeRelative(ref r, ref seg)) => {
                unknown_type()
            },
            _ => {unknown_type()},
        }
    }
}

fn after_analysis(state: &mut CompileState) {
    add_prog_item(unknown_type_item());
    struct Visitor;
    impl<'hir> itemlikevisit::ItemLikeVisitor<'hir> for Visitor {
        fn visit_item(&mut self, i: &'hir hir::Item) {
            match i.node {
                Item_::ItemStruct(ref var, ref gen) => {
                    let fields = match *var {
                        VariantData::Struct(ref structs,_)
                        | VariantData::Tuple(ref structs,_)=> {
                            structs.into_iter()
                            .map(|f|ast::Field::from(f))
                            .collect::<Vec<_>>()
                        },
                        VariantData::Unit(_) => {Vec::new()},
                    };
                    add_prog_item(ast::Item::StructDefn(ast::StructDefn{
                        name: ast::Identifier::from(i),
                        fields:fields,
                        // TODO: get data
                        parameter_kinds:Vec::new(),
                        where_clauses:Vec::new(),
                    })); 
                },
                // TODO: translate traits and impls
                Item_::ItemTrait(_, ref gen, ref par, ref items) => {

                },
                Item_::ItemImpl(_, _, _, ref gen, ref tr, ref ty, ref items) => {

                },
                _ => {}
            }
        }
        fn visit_trait_item(&mut self, _trait_item: &'hir hir::TraitItem) {}
        fn visit_impl_item(&mut self, _impl_item: &'hir hir::ImplItem) {}
    }
    state.hir_crate.unwrap().visit_all_item_likes(&mut Visitor);
}

pub fn parse_file(filename: String) -> Result<ast::Program,> {

    // Taken from https://github.com/Manishearth/rust-clippy/pull/911.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    let find_sysroot = match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => {
            option_env!("RUST_SYSROOT")
                .expect(
                    "need to specify RUST_SYSROOT env var or use rustup or multirust",
                )
                .to_owned()
        }
    };

    let mut args = Vec::new();
    args.push(String::from("rustc"));
    args.push(String::from("--sysroot"));
    args.push(find_sysroot);

    args.push(filename);
    
    let mut builder = ParseCompilerCalls{default: RustcDefaultCalls};
    rustc_driver::run_compiler(&args, &mut builder, None, None);
    Ok(ast::Program{items:get_prog()})
}
