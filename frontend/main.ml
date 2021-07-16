open Cmdliner
open Extra
open Panic.Simple
open Project
open Version

(* Standard file and directory names. *)

let rc_project_file   = "rc-project.toml"
let dune_project_file = "dune-project"
let coq_project_file  = "_CoqProject"
let rc_dir_name       = "proofs"

let code_file_name    = "generated_code.v"
let spec_file_name    = "generated_spec.v"
let proof_file_name   = Printf.sprintf "generated_proof_%s.v"
let proofs_file_name  = "proof_files"

let default_coqdir base = ["refinedc"; "project"; base]

(* RefinedC include directory (containing [refinedc.h]). *)
let refinedc_include : string option =
  try
    let opam_prefix = Sys.getenv "OPAM_SWITCH_PREFIX" in
    Some(Filename.concat opam_prefix "lib/refinedc/include")
  with Not_found -> None

(* The RefinedC tooling assumes a specific structure of the working directory.
   It is organized in a "RefinedC project", that can be set up with a provided
   command. Further actions maintain several invariants, like the existence of
   certain files.

   A RefinedC project, when it is initialized, contains the following files in
   its root directory:
    - [rc_project_file] containing certain project metadata,
    - [dune_project_file] containing the build system setup for Coq,
    - [coq_project_file] containing editor setup for Coq.
   These files are generated, and should not be modified directly. These files
   all have special, reserved names, that should not be used for other files.

   When checking a C source file, say ["src/dir/file.c"], RefinedC creates the
   special directory ["src/dir/" ^ rc_dir_name] if it does not already exists,
   and it also creates a directory ["file"] inside it (having the same name as
   the C source file, without the extension). This directory then contains all
   the generated (Coq) files corresponding to ["src/dir/file.c"]. For example,
   it would contain the code file [code_file_name].

   When checking another file of the same directory, a similar directory (with
   the base name of the file) is created under the special RefinedC directory.
   For example, the project source tree may look like the following:
   [{|
     .
     ├── _CoqProject
     ├── dune-project
     ├── lib
     │   ├── proofs
     │   │   └── socket
     │   │       ├── generated_code.v
     │   │       └── generated_spec.v
     │   └── socket.c
     ├── rc-project.toml
     └── src
         ├── client
         │   ├── client.c
         │   ├── lib.c
         │   └── proofs
         │       ├── client
         │       │   ├── generated_code.v
         │       │   └── generated_spec.v
         │       └── lib
         │           ├── generated_code.v
         │           └── generated_spec.v
         └── server
             ├── proofs
             │   └── server
             │       ├── generated_code.v
             │       └── generated_spec.v
             └── server.c
   |}]
   The Coq qualification for each source file is determined by the Coq logical
   directory chosen at project creation (which defaults to something using the
   directory name if possible). Using the example above, and assuming that the
   Coq logical directory name of the project is ["refinedc.project.my_server"]
   then ["src/client/proofs/client/generated_code.v"] is mapped to module name
   ["refinedc.project.my_server.src.client.generated_code"] in Coq.

   A directory corresponding to the generated code of a C source file also has
   a ["dune"] file, that controls its building. It is automatically generated,
   and automatically updated in case of changes.

   The user can freely add Coq files (provided they do not have reserved names
   like [code_file_name], [spec_file_name] or [proof_file_name s] where [s] is
   a potential C function name) to directories corresponding to any C file.

   TODO Find a better way, with a specific directory?

   RefinedC relies on file [proofs_file_name], placed next to generated files,
   to identify the currently valid proof files. When the user removes or moves
   a function spec, a proof file may no longer correspond to anything. In that
   case it is deleted by RefinedC automatically upon generation. *)

type config =
  { cpp_config  : Cerb_wrapper.cpp_config
  ; no_locs     : bool
  ; no_analysis : bool
  ; no_build    : bool }

(* Main entry point. *)
let run : config -> string -> unit = fun cfg c_file ->
  (* Set the printing flags. *)
  if cfg.no_locs then
    begin
      Coq_pp.print_expr_locs := false;
      Coq_pp.print_stmt_locs := false
    end;
  (* Split the file path into a file name and absolute directory path. *)
  let c_file =
    try Filename.realpath c_file with Invalid_argument(_) ->
      panic "File [%s] disappeared..." c_file
  in
  let c_file_name = Filename.basename c_file in
  let c_file_name_no_ext = Filename.remove_extension c_file_name in
  let c_file_dir = Filename.dirname c_file in
  (* Locate the RefinedC project root and the relitive logical directory. *)
  let find_root_and_dir_path dir =
    let rec find acc dir =
      let rc_project = Filename.concat dir rc_project_file in
      if Sys.file_exists rc_project then
        (dir, acc)
      else
       let parent = Filename.dirname dir in
       if parent = dir then raise Not_found;
       find (Filename.basename dir :: acc) parent
    in
    find [] dir
  in
  let (root_dir, c_file_dir_path) =
    try find_root_and_dir_path c_file_dir with Not_found ->
      panic "No RefinedC project can be located for file [%s]." c_file
  in
  (* Read the project configuration from the project file. *)
  let project_config =
    let project_file = Filename.concat root_dir rc_project_file in
    try
      if Sys.is_directory project_file then
        panic "Invalid project file [%s] (directory)." project_file;
      read_project_file project_file
    with Sys_error(_) ->
      panic "Error while reading the project file [%s]." project_file
  in
  (* Compute the base Coq logical path for the files. *)
  let file_coq_dir = project_config.project_coq_root @ c_file_dir_path in
  let path = String.concat "." file_coq_dir ^ "." ^ c_file_name_no_ext in
  (* Prepare the output folder if need be. *)
  let file_rc_dir = Filename.concat c_file_dir rc_dir_name in
  if not (Sys.file_exists file_rc_dir) then Unix.mkdir file_rc_dir 0o755;
  let output_dir = Filename.concat file_rc_dir c_file_name_no_ext in
  if not (Sys.file_exists output_dir) then
    begin
      Unix.mkdir output_dir 0o755;
      (* Add the mapping to the Coq project file for editors. *)
      let dune_dir_path =
        let relative_path = Filename.relative_path root_dir c_file_dir in
        let path =
          if relative_path = Filename.current_dir_name then "_build/default"
          else Filename.concat "_build/default" relative_path
        in
        let path = Filename.concat path rc_dir_name in
        Filename.concat path c_file_name_no_ext
      in
      let coq_project_path = Filename.concat root_dir coq_project_file in
      let new_line = Printf.sprintf "-Q %s %s" dune_dir_path path in
      let lines = try read_file coq_project_path with Sys_error(_) -> [] in
      if not (List.mem new_line lines) then
        append_file (Filename.concat root_dir coq_project_file) [new_line]
    end;
  (* Paths to the output files. *)
  let code_file = Filename.concat output_dir code_file_name in
  let spec_file = Filename.concat output_dir spec_file_name in
  let proof_of_file id = Filename.concat output_dir (proof_file_name id) in
  let proof_files_file = Filename.concat output_dir proofs_file_name in
  let dune_file = Filename.concat output_dir "dune" in
  (* Prepare the CPP configuration. *)
  let cpp_config =
    let cpp_I =
      let project_include =
        List.map (Filename.concat root_dir) project_config.project_cpp_include
      in
      let cpp_include = cfg.cpp_config.cpp_I @ project_include in
      match (refinedc_include, project_config.project_cpp_with_rc) with
      | (_      , false) -> cpp_include
      | (Some(d), true ) -> d :: cpp_include
      | (None   , true ) ->
          panic "Unable to locate the RefinedC include directory."
    in
    {cfg.cpp_config with cpp_I}
  in
  (* Parse the comment annotations. *)
  let open Comment_annot in
  let ca = parse_annots (Cerb_wrapper.cpp_lines cpp_config c_file) in
  let ctxt = List.map (fun s -> "Context " ^ s) ca.ca_context in
  (* Do the translation to Ail, analyse, and generate our AST. *)
  Sys.chdir root_dir; (* Move to the root to get relative paths. *)
  let c_file = Filename.relative_path root_dir c_file in
  let ail_ast = Cerb_wrapper.c_file_to_ail cpp_config c_file in
  if not cfg.no_analysis then Warn.warn_file ail_ast;
  let coq_ast = Ail_to_coq.translate c_file ail_ast in
  (* Generate the code file. *)
  let open Coq_pp in
  let mode = Code(root_dir, ca.ca_code_imports) in
  write mode code_file coq_ast;
  (* Generate the spec file. *)
  let mode = Spec(path, ca.ca_imports, ca.ca_inlined, ca.ca_typedefs, ctxt) in
  write mode spec_file coq_ast;
  (* Compute the list of proof files to generate. *)
  let to_generate =
    let not_inlined (_, def_or_decl) =
      let open Coq_ast in
      match def_or_decl with
      | FDef(def) when is_inlined def -> false
      | _                             -> true
    in
    let fs = List.filter not_inlined coq_ast.functions in
    let files = List.map (fun (id, _) -> proof_of_file id) fs in
    List.sort_uniq String.compare files
  in
  (* Delete obsolete proof files. *)
  let already_generated =
    let files = try read_file proof_files_file with Sys_error(_) -> [] in
    List.map (Filename.concat output_dir) files
  in
  let delete_when_obsolete fname =
    if not (List.mem fname to_generate) then
      try Sys.remove fname with Sys_error(_) -> ()
  in
  List.iter delete_when_obsolete already_generated;
  (* Write the new list of proof files. *)
  write_file proof_files_file (List.map Filename.basename to_generate);
  (* Generate the proof files. *)
  let proof_imports = ca.ca_imports @ ca.ca_proof_imports in
  let write_proof (id, def_or_decl) =
    let open Coq_ast in
    match def_or_decl with
    | FDec(_)                       -> ()
    | FDef(def) when is_inlined def -> ()
    | FDef(def)                     ->
    let mode = Fprf(path, def, proof_imports, ctxt, proof_kind def) in
    write mode (proof_of_file id) coq_ast
  in
  List.iter write_proof coq_ast.functions;
  (* Generate the dune file. *)
  let theories =
    let glob = List.map coq_path_to_string project_config.project_theories in
    let imports = ca.ca_imports @ ca.ca_proof_imports @ ca.ca_code_imports in
    let imports = List.sort_uniq Stdlib.compare imports in
    ignore imports; (* TODO some dependency analysis based on [imports]. *)
    List.sort_uniq String.compare (List.filter (fun s -> s <> path) (ca.ca_requires @ glob))
  in
  write_file dune_file [
    "; Generated by [refinedc], do not edit.";
    "(coq.theory";
    " (flags -w -notation-overridden -w -redundant-canonical-projection)";
    Printf.sprintf " (name %s)" path;
    Printf.sprintf " (theories %s))" (String.concat " " theories);
  ];
  (* Run Coq type-checking. *)
  if not (cfg.no_build || project_config.project_no_build) then
    begin
      Sys.chdir output_dir;
      match Sys.command "dune build --display=short" with
      | 0           ->
          Format.printf "File [%s] successfully checked.\n%!" c_file
      | i           ->
          panic "The call to [dune] returned with error code %i." i
      | exception _ ->
          panic "The call to [dune] failed for some reason."
    end

let cpp_I =
  let doc =
    "Add the directory $(docv) to the list of directories to be searched for \
     header files during preprocessing."
  in
  let i = Arg.(info ["I"] ~docv:"DIR" ~doc) in
  Arg.(value & opt_all dir [] & i)

let cpp_include =
  let doc =
    "Add an include for the file $(docv) at the beginning of the source file."
  in
  let i = Arg.(info ["include"] ~docv:"FILE" ~doc) in
  Arg.(value & opt_all file [] & i)


let cpp_nostdinc =
  let doc =
    "Do not search the standard system directories for header files. Only \
     the directories explicitly specified with $(b,-I) options are searched."
  in
  Arg.(value & flag & info ["nostdinc"] ~doc)

let cpp_D =
  let doc =
    "Do not search the standard system directories for header files. Only \
     the directories explicitly specified with $(b,-I) options are searched."
  in
  let i = Arg.(info ["D"] ~docv:"MACRODEF" ~doc) in
  Arg.(value & opt_all string [] & i)

let cpp_config =
  let build cpp_I cpp_include cpp_nostdinc cpp_D =
    Cerb_wrapper.{cpp_I; cpp_include; cpp_nostdinc; cpp_D}
  in
  Term.(pure build $ cpp_I $ cpp_include $ cpp_nostdinc $ cpp_D)

let no_analysis =
  let doc =
    "Disable the extra analyses (and the corresponding warnings) that are \
     performed on the source code by default. There are two such analyses. \
     (1) A warning is issued when the address of a local variable whose \
     scope is not that of the function is taken. Indeed, if that happens \
     then variables can potentially escape their lifetime (which is only \
     active in the block they are defined in) since all local variable are \
     hoisted to the function scope by RefiendC. (2) A warning is issued when \
     there is potential non-determinism in evaluation of expressions. This \
     is a problem since C has a loose ordering of expression evaluation, \
     while RefiendC has a fixed left-to-right evaluation order. Note that \
     these two analyses are over-approximations."
  in
  Arg.(value & flag & info ["no-extra-analysis"] ~doc)

let no_locs =
  let doc =
    "Do not output any location information in the generated Coq files."
  in
  Arg.(value & flag & info ["no-locs"] ~doc)

let no_build =
  let doc =
    "Do not build Coq object files after generation."
  in
  Arg.(value & flag & info ["no-build"] ~doc)

let opts : config Term.t =
  let build cpp_config no_analysis no_locs no_build =
    { cpp_config ; no_analysis ; no_locs ; no_build }
  in
  Term.(pure build $ cpp_config $ no_analysis $ no_locs $ no_build)

let c_file =
  let doc = "C language source file." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let check_cmd =
  let open Term in
  let term = pure run $ opts $ c_file in
  let doc = "Run RefiendC on the given C file." in
  (term, info "check" ~version ~doc)

(* Preprocessing command (useful for debugging). *)

let run_cpp config c_file =
  output_lines stdout (Cerb_wrapper.cpp_lines config c_file);
  flush stdout

let cpp_cmd =
  let doc = "Print the result of the Cerberus preprocessor to stdout." in
  Term.(pure run_cpp $ cpp_config $ c_file),
  Term.info "cpp" ~version ~doc

(* Ail printing command (useful for debugging). *)

let run_ail config c_file =
  let ail_ast = Cerb_wrapper.c_file_to_ail config c_file in
  Cerb_wrapper.print_ail ail_ast

let ail_cmd =
  let doc = "Print the Cerberus Ail AST of the given C file to stdout." in
  Term.(pure run_ail $ cpp_config $ c_file),
  Term.info "ail" ~version ~doc

(* Cleaning command. *)

let run_clean soft c_file =
  (* Split the file path into a file name and absolute directory path. *)
  let c_file_name = Filename.basename c_file in
  let c_file_name_no_ext = Filename.remove_extension c_file_name in
  let c_file_dir =
    let c_file_dir = Filename.dirname c_file in
    try Filename.realpath c_file_dir with Invalid_argument(_) ->
      panic "Directory [%s] disappeared..." c_file_dir
  in
  (* Check that the C source file is indeed in a RefinedC project. *)
  let find_root_and_dir_path dir =
    let rec find acc dir =
      let rc_project = Filename.concat dir rc_project_file in
      if Sys.file_exists rc_project then
        (dir, acc)
      else
       let parent = Filename.dirname dir in
       if parent = dir then raise Not_found;
       find (Filename.basename dir :: acc) parent
    in
    find [] dir
  in
  let (root_dir, c_file_dir_path) =
    try find_root_and_dir_path c_file_dir with Not_found ->
      panic "No RefinedC project can be located for file [%s]." c_file
  in
  (* Read the project configuration from the project file. *)
  let project_config =
    let project_file = Filename.concat root_dir rc_project_file in
    try
      if Sys.is_directory project_file then
        panic "Invalid project file [%s] (directory)." project_file;
      read_project_file project_file
    with Sys_error(_) ->
      panic "Error while reading the project file [%s]." project_file
  in
  (* Compute the base Coq logical path for the files. *)
  let file_coq_dir = project_config.project_coq_root @ c_file_dir_path in
  (* Compute the relevant directory and file paths. *)
  let rc_dir = Filename.concat c_file_dir rc_dir_name in
  let gen_dir = Filename.concat rc_dir c_file_name_no_ext in
  let dune_file = Filename.concat gen_dir "dune" in
  let proofs_file = Filename.concat gen_dir proofs_file_name in
  let code_file = Filename.concat gen_dir code_file_name in
  let spec_file = Filename.concat gen_dir spec_file_name in
  let proof_files =
    let files = try read_file proofs_file with Sys_error(_) -> [] in
    List.map (Filename.concat gen_dir) files
  in
  (* Compute the list of files to delete, and delete them. *)
  let all = [code_file; spec_file; dune_file; proofs_file] @ proof_files in
  List.iter (fun f -> try Sys.remove f with Sys_error(_) -> ()) all;
  (* Check if the generated directories are empty and if so delete them. *)
  let all_dirs = [gen_dir; rc_dir] in
  let rmdir dir =
    let files = try Sys.readdir dir with Sys_error(_) -> [||] in
    if Array.length files = 0 then
      ignore (Sys.command (Printf.sprintf "rm -rf %s" dir))
  in
  List.iter rmdir all_dirs;
  (* Delete the Coq project mapping for the file. *)
  if not soft then
  let path = String.concat "." file_coq_dir ^ "." ^ c_file_name_no_ext in
  let dune_dir_path =
    let relative_path = Filename.relative_path root_dir c_file_dir in
    let path = Filename.concat "_build/default" relative_path in
    let path = Filename.concat path rc_dir_name in
    Filename.concat path c_file_name_no_ext
  in
  let coq_project_path = Filename.concat root_dir coq_project_file in
  let line = Printf.sprintf "-Q %s %s" dune_dir_path path in
  let lines = try read_file coq_project_path with Sys_error(_) -> [] in
  if List.mem line lines then
    begin
      let new_lines = List.filter (fun s -> s <> line) lines in
      write_file coq_project_path new_lines
    end

let soft =
  let doc =
    "Do not remove the corresponding entry from the `_CoqProject' file."
  in
  Arg.(value & flag & info ["soft"] ~doc)

let clean_cmd =
  let doc = "Delete all the generated files for the given C source file." in
  Term.(pure run_clean $ soft $ c_file),
  Term.info "clean" ~version ~doc

(* Project initialization command. *)

let check_coqdir_member id =
  (* Empty string is invalid. *)
  if String.length id = 0 then
    invalid_arg "invalid empty Coq directory member.";
  (* Only accept characters and underscores. *)
  let check_char c =
    match c with
    | 'a'..'z' | 'A'..'Z' | '_' -> ()
    | _                         ->
        invalid_arg "invalid Coq directory member (contains %C)." c;
  in
  String.iter check_char id;
  (* Should not start with an underscore. *)
  if id.[0] = '_' then
    invalid_arg "invalid Coq directory member (starts with '_')."

let init : string list option -> unit = fun coqdir ->
  (* Read the current working directory. *)
  let wd =
    try Filename.realpath (Sys.getcwd ()) with Invalid_argument(_) ->
      panic "Error while reading the current working directory."
  in
  (* Files to generate. *)
  let rc_project_path = Filename.concat wd rc_project_file in
  let dune_project_path = Filename.concat wd dune_project_file in
  let coq_project_path = Filename.concat wd coq_project_file in
  (* Check for an existing project. *)
  if Sys.file_exists rc_project_path then
    panic "A RefinedC project already exists here.";
  (* Check for conflicting project files in subdirectories. *)
  let file_check is_dir path =
    let dir = Filename.dirname path in
    let base = Filename.basename path in
    if base = rc_project_file then
      if is_dir then panic "Subdirectory [%s] uses a reserved name." path
      else panic "A RefinedC project exists in directory [%s]." dir
    else if base = dune_project_file then
      if is_dir then panic "Subdirectory [%s] uses a reserved name." path
      else panic "A [%s] file exists in directory [%s]." dune_project_file dir
    else if base = coq_project_file then
      if is_dir then panic "Subdirectory [%s] uses a reserved name." path
      else panic "A [%s] file exists in directory [%s]." dune_project_file dir
    else if base = rc_dir_name then
      if is_dir then panic "Directory [%s] uses a reserved name." path
      else panic "File [%s] uses a reserved name." path
    else ()
  in
  Filename.iter_files ~ignored_dirs:[".git"; "_build"] wd file_check;
  (* Check for conflicting projects in parent directories. *)
  let rec check_parents dir =
    let check_dir dir =
      (* Avoid nested RefinedC projects for sanity. *)
      let file = Filename.concat dir rc_project_file in
      if Sys.file_exists file then begin
        if Sys.is_directory file then
          panic "Parent directory [%s] has a reserved name." file;
        panic "Nested under RefinedC project [%s]." file
      end;
      (* Avoid nested dune workspaces, leads to problems. *)
      let file = Filename.concat dir dune_project_file in
      if Sys.file_exists file then begin
        if Sys.is_directory file then
          panic "Parent directory [%s] has a reserved name." file;
        panic "Nested under RefinedC project [%s]." file
      end
      (* Coq project files should be OK. *)
    in
    let parent = Filename.dirname dir in
    if parent <> dir then (check_dir parent; check_parents parent)
  in
  check_parents wd;
  (* Build the Coq directory, using a possible CLI argument. *)
  let coqdir =
    match coqdir with Some(d) -> d | None ->
    let base = Filename.basename wd in
    try check_coqdir_member base; default_coqdir base
    with Invalid_argument(msg) ->
      panic "Current directory name is an %s" msg
  in
  (* Now we are safe, generate the project files. *)
  write_project_file rc_project_path (default_project_config coqdir);
  write_file dune_project_path [
    "(lang dune 2.7)";
    "(using coq 0.2)";
    "; Generated by [refinedc], do not edit.";
  ];
  write_file coq_project_path [
    "# Generated by [refinedc], do not edit.";
    "-arg -w -arg -notation-overridden";
    "-arg -w -arg -redundant-canonical-projection";
  ];
  (* Reporting. *)
  let coqdir = String.concat "." coqdir in
  Format.printf "Initialized a RefinedC project in [%s].\n" wd;
  Format.printf "Using the Coq logical directory [%s].\n%!" coqdir

let coqdir =
  let doc =
    "Specify the logical Coq directory under which the created verification \
    project is to be placed. The argument is expected to be a dot-sperated \
    list of identifiers formed of letters and underscores (but not in first \
    position). If no explicit Coq directory is given then it defaults to \
    [refinedc.project.DIRNAME], where DIRNAME is the current directory name. \
    If DIRNAME is not a valid identifier then the command fails."
  in
  let coqdir =
    let parse s =
      let ids = String.split_on_char '.' s in
      try List.iter check_coqdir_member ids; Ok ids
      with Invalid_argument(msg) -> Error (`Msg msg)
    in
    let pp fmt ids = Format.pp_print_string fmt (String.concat "." ids) in
    Arg.conv ~docv:"COQDIR" (parse, pp)
  in
  let i = Arg.(info ["coqdir"] ~docv:"COQDIR" ~doc) in
  Arg.(value & opt (some coqdir) None & i)

let init_cmd =
  let doc = "Create a new RefinedC project in the current directory." in
  Term.(pure init $ coqdir),
  Term.info "init" ~version ~doc

(* A few trivial commands. *)

let print_version () =
  Format.printf "RefinedC version: %s\nRelying on Cerberus version: %s\n%!"
    Version.version Cerb_frontend.Version.version

let version_cmd =
  let doc = "Show detailed version information for RefinedC." in
  Term.(const print_version $ const ()),
  Term.info "version" ~version ~doc

let help_cmd =
  let doc = "Show the main help page for RefinedC." in
  Term.(ret (const (`Help (`Pager, None)))),
  Term.info "help" ~version ~doc

let default_cmd =
  let doc = "RefinedC program verification framework." in
  Term.(ret (const (`Help(`Pager, None)))),
  Term.info "refinedc" ~version ~doc

(* Entry point. *)
let _ =
  let cmds =
    [ init_cmd ; cpp_cmd ; ail_cmd ; check_cmd ; clean_cmd
    ; help_cmd ; version_cmd ]
  in
  Term.(exit (eval_choice default_cmd cmds))
