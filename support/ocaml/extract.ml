open Typedtree

let clean value =
  String.map (function '\t' | '\n' | '\r' -> ' ' | character -> character) value

let emit kind target location inferred_type =
  let start = location.Location.loc_start in
  let finish = location.Location.loc_end in
  Printf.printf "%s\t%s\t%s\t%d\t%d\t%d\t%d\t%s\n"
    kind (clean target) (clean start.Lexing.pos_fname)
    start.Lexing.pos_lnum (start.Lexing.pos_cnum - start.Lexing.pos_bol)
    finish.Lexing.pos_lnum (finish.Lexing.pos_cnum - finish.Lexing.pos_bol)
    (clean inferred_type)

let inferred_type expression =
  Format.asprintf "%a" Printtyp.type_expr expression.exp_type

let expression iterator expression =
  (match expression.exp_desc with
  | Texp_apply (({ exp_desc = Texp_ident (path, _, _); _ } as callee), _) ->
      emit "direct" (Path.name path) expression.exp_loc (inferred_type callee)
  | Texp_apply (callee, _) ->
      emit "indirect" "" expression.exp_loc (inferred_type callee)
  | Texp_send _ ->
      emit "indirect" "object-method" expression.exp_loc (inferred_type expression)
  | _ -> ());
  Tast_iterator.default_iterator.expr iterator expression

let inspect filename =
  let information = Cmt_format.read_cmt filename in
  let iterator = { Tast_iterator.default_iterator with expr = expression } in
  match information.Cmt_format.cmt_annots with
  | Cmt_format.Implementation structure -> iterator.structure iterator structure
  | Cmt_format.Partial_implementation parts ->
      Array.iter
        (function
          | Cmt_format.Partial_structure structure ->
              iterator.structure iterator structure
          | Cmt_format.Partial_structure_item item ->
              iterator.structure_item iterator item
          | Cmt_format.Partial_expression expression ->
              iterator.expr iterator expression
          | _ -> ())
        parts
  | _ -> ()

let () =
  if Array.length Sys.argv <> 2 then (
    prerr_endline "usage: diffkit-ocaml-extract FILE.cmt";
    exit 2);
  inspect Sys.argv.(1)
