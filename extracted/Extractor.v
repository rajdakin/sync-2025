From Reactive.Translations Require LustreAstToLustre LustreOrderedToImp LustreOrdering.
From Reactive.Props Require Axioms.

From Corelib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.

#[local] Set Warnings "-extraction-default-directory".

Extract Constant String.compare => "StringImpl.compare".
Extract Constant LustreOrdering.node_ordering => "Ordered.node_ordering".
Extract Constant Axioms.ABORT_FIXME => "Abort.aBORT_FIXME".

Separate Extraction
  LustreOrdering.translate_node
  LustreOrderedToImp.translate_node
  LustreAstToLustre.check_node_prop
  Stream.from.
