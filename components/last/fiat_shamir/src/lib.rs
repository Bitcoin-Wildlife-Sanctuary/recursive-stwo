use circle_plonk_dsl_circle::CirclePointQM31Var;
use circle_plonk_dsl_data_structures::PlonkWithAcceleratorLookupElementsVar;
use circle_plonk_dsl_fields::QM31Var;

pub struct FiatShamirResults {
    pub lookup_elements: PlonkWithAcceleratorLookupElementsVar,
    pub random_coeff: QM31Var,
    pub oods_point: CirclePointQM31Var,
}
