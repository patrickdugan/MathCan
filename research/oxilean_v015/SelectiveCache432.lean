import Cache.Requests

/-! Selective read-only cache driver. Uses the pinned official hashing and
transport implementations, starting only from the requested Taylor roots.
The upstream cache CLI also starts from Mathlib.lean, which would require the
entire source tree. No proof source, hash rule, URL, or artifact is modified. -/
open Lean Cache IO Hashing Requests

def main (args : List String) : IO Unit := do
  let sp ← getSrcSearchPath
  let ctx : CacheM.Context := {mathlibDepPath := ".", srcSearchPath := sp}
  let action : CacheM Unit := do
    let hashRoot ← getRootHash
    let hashAll : HashM Unit := do
      for arg in args do
        let name := (arg.splitOn ".").foldl Name.str Name.anonymous
        let path ← Lean.findLean sp name
        discard <| getHash name path
    let (_,memo) ← hashAll.run {rootHash := hashRoot}
    IO.println s!"Selective cache closure: {memo.hashMap.size} modules"
    let parallel ← validateCurl
    getFiles MATHLIBREPO memo.hashMap false false parallel false
    let config ← mkLeanTarConfig memo.hashMap
    IO.FS.writeFile (CACHEDIR / "extraction-plan.json") (Lean.Json.compress (toJson config))
    let modules ← memo.hashMap.toArray.mapM fun (mod, hash) => do
      let paths ← mkBuildPaths mod
      pure <| Lean.Json.mkObj [("module", toJson mod.toString),
        ("file", toJson (CACHEDIR / hash.asLTar).toString),
        ("paths", toJson (paths.map fun p => p.1.toString))]
    IO.FS.writeFile (CACHEDIR / "module-plan.json") (Lean.Json.compress (toJson modules))
  ReaderT.run action ctx
