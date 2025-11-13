From Reactive.Datatypes Require Array Hashtable.
From Reactive.Translations Require LustreAstToLustre LustreOrderedToImp LustreOrdering LustreToTiming.
From Reactive.Props Require Axioms.

From Corelib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.

#[local] Set Warnings "-extraction-default-directory".

Extract Constant Array.t "'a" => "'a array".
Extract Constant Array.length "'a" => "Stdlib.Array.length".
Extract Constant Array.make "'a" => "Stdlib.Array.make".
Extract Constant Array.get "'a" => "Stdlib.Array.get".
Extract Constant Array.set "'a" => "(fun a i x -> Stdlib.Array.set a i x; a)".
Extract Constant Hashtable.t "'a" "'b" => "('a, 'b) Stdlib.Hashtbl.t".
Extract Constant Hashtable.create "'a" "'b" => "(fun n -> Stdlib.Hashtbl.create n)".
Extract Constant Hashtable.add "'a" "'b" => "(fun m x y -> Stdlib.Hashtbl.add m x y; m)".
Extract Constant Hashtable.find "'a" "'b" => "Stdlib.Hashtbl.find".
Extract Constant Hashtable.find_opt "'a" "'b" => "Stdlib.Hashtbl.find_opt".
Extract Constant LustreOrdering.List_mem => "Stdlib.List.mem". (* Small optimization? *)
Extract Constant String.compare => "StringImpl.compare".

Extract Constant Axioms.ABORT_FIXME => "Abort.aBORT_FIXME".

Separate Extraction
  LustreAstToLustre.check_node_prop
  LustreToTiming.translate_node
  LustreOrdering.translate_node
  LustreOrderedToImp.translate_node
  Stream.from.
