import Lean.Data.Json

/-! # A reduced fixture written as a checked entry model

A model without `header.modelVersion`, without `header.locales` or without `content.modelInfo` builds,
and its consistency check then fails without a class (peer KF650; the
[model frame members](../../../docs/sources/model-structure-and-declaration-probes.md#src-model-frame-members)
checkpoint). Locks whose fixtures reduce a model to the members they measure complete the frame here
rather than each restating it. -/

namespace A12Kernel.Dm

open Lean

private def withDefault (parent : Json) (key : String) (value : Json) : Json :=
  if (parent.getObjVal? key).isOk then parent else parent.setObjVal! key value

/-- `model` with `header.modelVersion`, `header.locales` declaring "en_US" and a named
`content.modelInfo`, each added only where the fixture writes none, so a fixture measuring one of these
members keeps its own value, `null` included. A model without `content` is returned unchanged. -/
def checkedEntryFrame (model : Json) : Json :=
  match model.getObjVal? "content" with
  | .error _ => model
  | .ok content =>
      let header := (model.getObjVal? "header").toOption.getD (Json.mkObj [])
      let header := withDefault (withDefault header "modelVersion" "28.4.0") "locales"
        (Json.arr #[Json.mkObj [("code", "en_US")]])
      (model.setObjVal! "header" header).setObjVal! "content"
        (withDefault content "modelInfo" (Json.mkObj [("name", "Fixture")]))

end A12Kernel.Dm
