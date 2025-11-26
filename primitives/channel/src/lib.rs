use circle_plonk_dsl_constraint_system::var::{AllocVar, Var};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_poseidon31::Poseidon2HalfVar;
use stwo::core::fields::m31::M31;

pub type HashVar = Poseidon2HalfVar;

#[derive(Clone)]
pub struct ChannelVar {
    pub n_sent: usize,
    pub digest: Poseidon2HalfVar,
}

impl Var for ChannelVar {
    type Value = [M31; 16];

    fn cs(&self) -> ConstraintSystemRef {
        self.digest.cs()
    }
}

impl ChannelVar {
    pub fn default(cs: &ConstraintSystemRef) -> Self {
        let n_sent = 0;
        let digest = Poseidon2HalfVar::zero(cs);
        Self { n_sent, digest }
    }

    pub fn mix_root(&mut self, root: &HashVar) {
        self.digest = Poseidon2HalfVar::permute_get_capacity(root, &self.digest);
        self.n_sent = 0;
    }

    pub fn draw_felts(&mut self) -> [QM31Var; 2] {
        let cs = self.cs();

        let n_sent = M31Var::new_constant(&cs, &M31::from(self.n_sent as u32));
        self.n_sent += 1;

        let n_sent = QM31Var::from(&n_sent);

        let left = Poseidon2HalfVar::from_qm31(&n_sent, &QM31Var::zero(&cs));
        Poseidon2HalfVar::permute_get_rate(&left, &self.digest).to_qm31()
    }

    pub fn mix_one_felt(&mut self, felt: &QM31Var) {
        let cs = self.cs();
        let left = Poseidon2HalfVar::from_qm31(&felt, &QM31Var::zero(&cs));
        self.digest = Poseidon2HalfVar::permute_get_capacity(&left, &self.digest);
        self.n_sent = 0;
    }

    pub fn mix_two_felts(&mut self, felt1: &QM31Var, felt2: &QM31Var) {
        let left = Poseidon2HalfVar::from_qm31(&felt1, &felt2);
        self.digest = Poseidon2HalfVar::permute_get_capacity(&left, &self.digest);
        self.n_sent = 0;
    }
}
