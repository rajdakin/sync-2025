From Reactive.Translations Require LustreOrderedToImp LustreOrdering.

From Coq Require Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.

#[local] Set Warnings "-extraction-default-directory".


Extract Constant LustreOrdering.node_ordering => "Ordered.node_ordering".

Separate Extraction
  LustreOrdering.translate_node
  LustreOrderedToImp.translate_node
  Stream.from.
