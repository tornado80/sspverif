# Commandline Client



## Subcommands

### Graph

Extracts the composition graph in the dot graph-format for further consumption.

```
ssp graph --output <OUTPUT> <DIRNAME>
```

The individual dotfiles can be converted to image files with the `dot` utility (graphviz)

```
dot -T svg outdir/Composition.dot > outdir/Composition.svg
```

