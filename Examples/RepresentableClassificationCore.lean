import SquareKit.Internal.RepresentableClassification

/-! Compatibility names for the #642 experiment, now implemented by the shared
production core. New clients can import the production module directly. -/
namespace Examples.RepresentableClassificationCore
export SquareKit.RepresentableClassification
  (Context Family representable represented representableMap represented_id
    representableGeneric represented_restrict represented_naturality
    represented_generic_source elements_eqToHom_hom raisedContext raisedSub
    raisedElements representableGenericHom family_map_heq family_map_identity_heq
    raisedSub_id raisedSub_comp System Evaluation)
namespace System
export SquareKit.RepresentableClassification.System
  (mk Data restrict restrict_id restrict_comp codes code code_reindex code_reindex_comp
    decode decode_reindex)
end System
namespace Evaluation
export SquareKit.RepresentableClassification.Evaluation (mk obj map component component_heq iso)
end Evaluation
end Examples.RepresentableClassificationCore
