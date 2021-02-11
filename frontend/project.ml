open Extra
open Panic.Simple

(** Representation of a Coq module path. *)
type coq_path = string list

let coq_path_to_string : coq_path -> string = String.concat "."

(** Project configuration (read from and written to a Toml file). *)
type project_config =
  { project_coq_root    : coq_path  (** Coq path of the project root. *)
  ; project_theories    : coq_path list (** Extra Coq (dune) theories. *)
  ; project_cpp_include : string list (** CPP include directories. *)
  ; project_cpp_with_rc : bool (** Use global RefinedC include directory? *)
  ; project_no_build    : bool (** Do not run the Coq compilation. *) }

(** [default_project_config coq_path] builds a default configuration for a new
    RefinedC project under Coq logical directory [coq_path]. *)
let default_project_config : coq_path -> project_config = fun coq_path ->
  { project_coq_root    = coq_path
  ; project_theories    = []
  ; project_cpp_include = []
  ; project_cpp_with_rc = true
  ; project_no_build    = false }

(** [read_project_file fname] reads a RefinedC project configuration from file
    [fname] (in Toml format). The function may raise [Sys_error] in case of an
    error when reading the configuration file. If the file is invalid then the
    program fails with exit code [1] after printing an explanation. *)
let read_project_file : string -> project_config = fun file ->
  let panic fmt = panic ("Broken project file [%s].\n" ^^ fmt) file in
  let toml =
    match Toml.Parser.from_filename file with
    | `Ok(table)     -> table
    | `Error(msg, _) -> panic "%s." msg
  in
  let coq_root = ref None in
  let theories = ref None in
  let cpp_include = ref None in
  let cpp_with_rc = ref None in
  let no_build = ref None in
  let handle_entry key value =
    let open TomlTypes in
    let section = Table.Key.to_string key in
    match (section, value) with
    | ("coq_root", TString(s)) -> coq_root := Some(s)
    | ("no_build", TBool(b)  ) -> no_build := Some(b)
    | ("coq"     , TTable(t) ) ->
        let handle_entry key value =
          let key = Table.Key.to_string key in
          match (key, value) with
          | ("extra_theories", TArray(NodeString(l))) -> theories := Some(l)
          | ("extra_theories", TArray(NodeEmpty)    ) -> theories := Some([])
          | ("extra_theories", _                    ) ->
              panic "Key [%s] should contain an array of strings." key
          | (_               , _                    ) ->
              panic "Key [%s] is invalid in section [%s]." key section
        in
        Table.iter handle_entry t
    | ("cpp"     , TTable(t) ) ->
        let handle_entry key value =
          let key = Table.Key.to_string key in
          match (key, value) with
          | ("include", TArray(NodeString(l))) -> cpp_include := Some(l)
          | ("include", TArray(NodeEmpty)    ) -> cpp_include := Some([])
          | ("include", _                    ) ->
              panic "Key [%s] should contain an array of strings." key
          | ("use_rc_include", TBool(b)      ) -> cpp_with_rc := Some(b)
          | ("use_rc_include", _             ) ->
              panic "Key [%s] should contain a boolean." key
          | (_               , _             ) ->
              panic "Key [%s] is invalid in section [%s]." key section
        in
        Table.iter handle_entry t
    | ("coq_root", _         ) ->
        panic "Key [%s] should contain a string" section
    | ("no_build", _         ) ->
        panic "Key [%s] should contain a boolean" section
    | ("coq"     , _         ) ->
        panic "Key [%s] should be a section." section
    | ("cpp"     , _         ) ->
        panic "Key [%s] should be a section." section
    | (_         , _         ) ->
        panic "Invalid section [%s]." section
  in
  TomlTypes.Table.iter handle_entry toml;
  let project_coq_root =
    match !coq_root with
    | None    -> panic "a [coq_root] entry is mandatory" file
    | Some(s) -> String.split_on_char '.' s
  in
  let project_theories =
    List.map (String.split_on_char '.') (Option.get [] !theories)
  in
  let project_cpp_include = Option.get [] !cpp_include in
  let project_cpp_with_rc = Option.get true !cpp_with_rc in
  let project_no_build = Option.get false !no_build in
  { project_coq_root ; project_theories ; project_cpp_include
  ; project_cpp_with_rc ; project_no_build }

(** [write_project_file config fname] writes the configuration [config] to the
    file [fname]. The function can raise [Sys_error] in case of a problem when
    opening the file for writing. *)
let write_project_file : string -> project_config -> unit = fun file pc ->
  let open TomlTypes in
  let coq_root = TString(coq_path_to_string pc.project_coq_root) in
  let theories =
    TArray(NodeString(List.map coq_path_to_string pc.project_theories))
  in
  let cpp_include = TArray(NodeString(pc.project_cpp_include)) in
  let cpp_with_rc = TBool(pc.project_cpp_with_rc) in
  let to_str v = Toml.Printer.string_of_value v in
  write_file file [
    "# Generated by [refinedc init].";
    "";
    "coq_root = " ^ to_str coq_root;
    "";
    "[cpp]";
    "include = " ^ to_str cpp_include;
    "use_rc_include = " ^ to_str cpp_with_rc;
    "";
    "[coq]";
    "extra_theories = " ^ to_str theories;
  ]
