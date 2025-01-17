use circle_plonk_dsl_circle::CirclePointQM31Var;
use circle_plonk_dsl_fields::QM31Var;

#[derive(Debug, Clone)]
pub struct PointSampleVar {
    pub point: CirclePointQM31Var,
    pub value: QM31Var,
}
