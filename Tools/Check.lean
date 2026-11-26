/-! # The local checks, and the way commits are made

`lake exe inets-check` runs every check that a commit must pass:

* `lake build`, with warnings as errors (set in `lakefile.toml`);
* the foundations of every constant of the library (`Tools/Axioms.lean`):
  only `propext`, `Quot.sound` and `Classical.choice`;
* `leanchecker --fresh` on the library;
* no line of a Lean file, or of `formalization.yaml`, over 100 characters;
* none of the three forbidden words in the library or its overview, but
  for the two sentences of the overview that name what is excluded;
* in `Challenges/`, exactly one open proof for each theorem a
  configuration lists, and `lake comparator --paranoid` accepting each;
* every declaration named in `formalization.yaml` exists, lies in the file
  given, rests on exactly the foundations listed, and, when a Comparator
  configuration is given, is one of its theorems.

`lake exe inets-check commit <message file> <paths…>` runs the checks,
commits the paths with the message, checks that the GitHub workflow of the
repository is switched off, pushes to `main`, and checks that no run of
the workflow started.  It uses `git` and `gh`. -/

open System

/-- Run a command, with its output shown, and fail unless it succeeds. -/
def run (cmd : String) (args : Array String) : IO Unit := do
  let child ← IO.Process.spawn { cmd, args }
  let code ← child.wait
  unless code == 0 do
    throw <| IO.userError s!"{cmd} {" ".intercalate args.toList} failed with {code}"

/-- Run a command and return what it prints, failing unless it succeeds. -/
def capture (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"{cmd} {" ".intercalate args.toList} failed:\n{out.stdout}{out.stderr}"
  return out.stdout ++ out.stderr

/-- The files under a directory with an extension. -/
partial def filesUnder (dir : FilePath) (ext : String) : IO (Array FilePath) := do
  if !(← dir.pathExists) then return #[]
  let mut acc := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then acc := acc ++ (← filesUnder e.path ext)
    else if e.path.extension == some ext then acc := acc.push e.path
  return acc.qsort (·.toString < ·.toString)

/-- The words that must not occur in the library, spelt so that this file
does not contain them. -/
def forbidden : List String := ["sor" ++ "ry", "native_" ++ "decide", "axi" ++ "om"]

/-- The two sentences of the overview that name what is excluded. -/
def allowed : List String := ["adds no " ++ "axi" ++ "om.", "three standard " ++ "axi" ++ "oms"]

/-- A string without spaces at its ends. -/
def trim (s : String) : String := s.trimAscii.toString

/-- Whether `s` occurs in `t`. -/
def occurs (s t : String) : Bool := (t.splitOn s).length > 1

/-- The number of times the word `w` occurs in `t`, as a whole word. -/
def wordCount (w t : String) : Nat :=
  let parts := t.splitOn w
  let ok (c : Option Char) : Bool := match c with
    | some c => !(c.isAlphanum || c == '_')
    | none => true
  (List.range (parts.length - 1)).countP fun i =>
    ok (parts[i]!.toList.getLast?) && ok (parts[i + 1]!.toList.head?)

/-- The quoted strings after `key` in a line-oriented text, one per line. -/
def quotedAfter (key : String) (line : String) : Option String :=
  match (trim line).splitOn key with
  | [pre, rest] =>
    if (trim pre).isEmpty || trim pre == "-" then
      match rest.splitOn "\"" with
      | _ :: v :: _ => some v
      | _ => none
    else none
  | _ => none

/-- The theorem names of a Comparator configuration. -/
def theoremNames (json : String) : List String :=
  match json.splitOn "\"theorem_names\"" with
  | [_, rest] =>
    match rest.splitOn "]" with
    | body :: _ => ((body.splitOn "\"").zipIdx.filter (·.2 % 2 == 1)).map (·.1)
    | [] => []
  | _ => []

structure Entry where
  decl : String
  file : String
  config : Option String
  axioms : List String
  deriving Inhabited

/-- The main results of `formalization.yaml`. -/
def entries (yaml : String) : List Entry := Id.run do
  let mut acc : List Entry := []
  let mut cur : Option Entry := none
  for line in yaml.splitOn "\n" do
    if let some d := quotedAfter "declaration:" line then
      if let some e := cur then acc := e :: acc
      cur := some { decl := d, file := "", config := none, axioms := [] }
    else if let some f := quotedAfter "file:" line then
      cur := cur.map fun e => { e with file := f }
    else if let some c := quotedAfter "comparator_config:" line then
      cur := cur.map fun e => { e with config := some c }
    else if occurs "axioms: [" line && cur.isSome then
      let body := ((line.splitOn "[")[1]!.splitOn "]")[0]!
      let names := (body.splitOn ",").map (fun s => (trim s).replace "\"" "")
      cur := cur.map fun e => { e with axioms := names.filter (!·.isEmpty) }
  if let some e := cur then acc := e :: acc
  return acc.reverse

def checks : IO Unit := do
  IO.println "== build"
  run "lake" #["build"]
  IO.println "== foundations of every constant"
  let ax ← capture "lake" #["env", "lean", "Tools/Axioms.lean"]
  IO.println (trim ax)
  let some lst := (ax.splitOn ("axi" ++ "oms: [")).getLast?.map (fun s => (s.splitOn "]")[0]!)
    | throw <| IO.userError "no list of foundations"
  for a in lst.splitOn "," do
    unless ["propext", "Quot.sound", "Classical.choice"].contains (trim a) do
      throw <| IO.userError s!"foundation not allowed: {trim a}"
  IO.println "== leanchecker"
  run "lake" #["env", "leanchecker", "--fresh", "InteractionNets"]
  IO.println "== lines and words"
  let lean := (← filesUnder "InteractionNets" "lean") ++ #[("InteractionNets.lean" : FilePath)]
  let others := (← filesUnder "Challenges" "lean") ++ (← filesUnder "Tools" "lean")
  for f in lean ++ others ++ #[("formalization.yaml" : FilePath)] do
    let lines := (← IO.FS.readFile f).splitOn "\n"
    for (l, i) in lines.zip (List.range lines.length) do
      if l.length > 100 then throw <| IO.userError s!"{f}:{i + 1} has {l.length} characters"
  for f in lean do
    let lines := (← IO.FS.readFile f).splitOn "\n"
    for (l, i) in lines.zip (List.range lines.length) do
      if forbidden.any (occurs · l) && !allowed.any (occurs · l) then
        throw <| IO.userError s!"{f}:{i + 1}: {l}"
  IO.println "== challenges"
  let mut listed := 0
  for c in ← filesUnder "Challenges" "json" do
    listed := listed + (theoremNames (← IO.FS.readFile c)).length
    run "lake" #["comparator", "--config", c.toString, "--paranoid"]
  let mut open_ := 0
  for f in ← filesUnder "Challenges" "lean" do
    open_ := open_ + wordCount ("sor" ++ "ry") (← IO.FS.readFile f)
  IO.println s!"listed theorems {listed}, open proofs {open_}"
  unless listed == open_ do throw <| IO.userError "open proofs and listed theorems differ"
  IO.println "== catalogue"
  let yaml ← IO.FS.readFile "formalization.yaml"
  let es := entries yaml
  if es.isEmpty then throw <| IO.userError "no main results in the catalogue"
  let src := "import InteractionNets\n" ++
    "\n".intercalate (es.map fun e => s!"#print {"axi" ++ "oms"} {e.decl}")
  IO.FS.writeFile ".lake/Catalogue.lean" src
  let out ← capture "lake" #["env", "lean", ".lake/Catalogue.lean"]
  for e in es do
    let short := (e.decl.splitOn ".").drop 1 |> ".".intercalate
    let body ← IO.FS.readFile e.file
    unless occurs s!"theorem {short} " body || occurs s!"theorem {short}\n" body do
      throw <| IO.userError s!"{e.decl} is not in {e.file}"
    let some line := (out.splitOn "\n").find? (occurs s!"'{e.decl}'")
      | throw <| IO.userError s!"{e.decl} not found"
    let got := if occurs "[" line then
        ((((line.splitOn "[")[1]!).splitOn "]")[0]!.splitOn ",").map trim
      else []
    unless got.toArray.qsort (· < ·) == e.axioms.toArray.qsort (· < ·) do
      throw <| IO.userError s!"{e.decl}: foundations {got}, catalogue says {e.axioms}"
    if let some c := e.config then
      unless (theoremNames (← IO.FS.readFile c)).contains e.decl do
        throw <| IO.userError s!"{e.decl} is not a theorem of {c}"
  IO.println s!"{es.length} entries"
  IO.println "ALL OK"

def repo := "repos/OnixResearch/inets"

def commit (msg : String) (paths : List String) : IO Unit := do
  checks
  run "git" (#["add"] ++ paths.toArray)
  run "git" #["commit", "-q", "-F", msg]
  let st := trim (← capture "gh" #["api", s!"{repo}/actions/workflows", "--jq",
    ".workflows[0].state"])
  unless st == "disabled_manually" do
    throw <| IO.userError s!"the workflow is {st}; not pushing"
  let before := trim (← capture "gh" #["api", s!"{repo}/actions/runs", "--jq", ".total_count"])
  run "git" #["push", "origin", "main"]
  IO.sleep 20000
  let after := trim (← capture "gh" #["api", s!"{repo}/actions/runs", "--jq", ".total_count"])
  IO.println s!"runs before {before}, after {after}"
  unless before == after do throw <| IO.userError "a run of the workflow started"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [] => checks
    | "commit" :: msg :: paths => commit msg paths
    | _ => IO.println "usage: inets-check [commit <message file> <paths...>]"
    return 0
  catch e =>
    IO.eprintln s!"CHECK FAILED: {e}"
    return 1
