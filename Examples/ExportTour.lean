    import LiterateLean
    import Examples.Bell
    open scoped LiterateLean

# Exporting the tour's circuit image

This command serializes the same typed SVG tree used by `#html Bell.program`.
It reads the program's static diagram and never runs a quantum backend. The SVG
keeps the renderer's coordinates, labels, and accessibility attributes; only React
attribute names and editor-dependent colors are adapted for a standalone image.

## Standalone SVG serialization

The exporter accepts text and ordinary elements only. An unexpected widget component
is an error rather than an incomplete image. Text and attribute values are escaped
before serialization, and the outer scrolling HTML container is omitted.

```lean
namespace TourExport

open Lean ProofWidgets

meta def escapeXml (value : String) : String :=
  value.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
    |>.replace "\"" "&quot;" |>.replace "'" "&apos;"

meta def svgAttribute (name : String) : String :=
  match name with
  | "strokeWidth" => "stroke-width"
  | "strokeDasharray" => "stroke-dasharray"
  | "fontSize" => "font-size"
  | "textAnchor" => "text-anchor"
  | _ => name

meta def attributeValue (value : Json) : String :=
  match value with
  | .str value => value.replace "var(--vscode-editor-background)" "#ffffff"
  | _ => value.compress

meta partial def serializeSvg : Html → Except String String
  | .text value => pure (escapeXml value)
  | .component .. => throw "Cannot export a dynamic widget as static SVG."
  | .element tag attributes children => do
      let attrs := attributes.foldl (fun result (name, value) =>
        result ++ s!" {svgAttribute name}=\"{escapeXml (attributeValue value)}\"") ""
      let theme := if tag == "svg" then
        " color=\"#17251e\" style=\"background:#ffffff;font-family:ui-monospace,monospace\"" else ""
      let body ← children.foldlM (fun result child => do
        pure (result ++ (← serializeSvg child))) ""
      pure s!"<{tag}{attrs}{theme}>{body}</{tag}>"

meta def bellSvg : Except String String := do
  let .element "div" _ #[svg] := (QASM.Diagram.ofProgram Bell.program).toHtml
    | throw "Expected the circuit renderer's SVG container."
  serializeSvg svg

end TourExport
```

## Regenerating the asset

From the repository root, first compile the imported standalone example, then run:

```sh
lake build QASM
mkdir -p .lake/build/lib/lean/Examples
lake env lean -o .lake/build/lib/lean/Examples/Bell.olean Examples/Bell.lean
lake env lean Examples/ExportTour.lean
```

The final command writes `docs/tour/bell.svg`, creating its directory when necessary.
A serializer or filesystem failure fails the command instead of retaining a partial SVG.

```lean
#eval do
  let svg ← match TourExport.bellSvg with
    | .ok svg => pure svg
    | .error message => throw (IO.userError message)
  IO.FS.createDirAll "docs/tour"
  IO.FS.writeFile "docs/tour/bell.svg" (svg ++ "\n")
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
