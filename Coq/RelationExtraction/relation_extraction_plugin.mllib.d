relation_extraction_plugin_MLLIB_DEPENDENCIES:= proof_scheme pred coq_stuff host2spec minimlgen fixpred reltacs proofgen fixpointgen relation_extraction g_relation_extraction
relation_extraction_plugin.cma:$(addsuffix .cmo,$(relation_extraction_plugin_MLLIB_DEPENDENCIES))
relation_extraction_plugin.cmxa relation_extraction_plugin.cmxs:$(addsuffix .cmx,$(relation_extraction_plugin_MLLIB_DEPENDENCIES))
