    import LiterateLean
    import Tests.Main
    open scoped LiterateLean

# Diagram extraction smoke scenario

The test fixture already contains loops, branches, gates, swaps, and measurements. This
evaluation derives the immutable presentation model directly from its canonical IR;
printing the value checks extraction without invoking HTML rendering or execution.

```lean
#eval QASM.Diagram.ofProgram QASMTests.DiagramProgram.program
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
