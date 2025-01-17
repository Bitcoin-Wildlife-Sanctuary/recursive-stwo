use circle_plonk_dsl_constraint_system::dvar::{AllocVar, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_poseidon31::Poseidon2HalfStateRef;
use stwo_prover::core::fields::m31::M31;

pub type HashVar = Poseidon2HalfStateRef;

#[derive(Clone)]
pub struct ChannelVar {
    pub n_sent: usize,
    pub digest: Poseidon2HalfStateRef,
}

impl DVar for ChannelVar {
    type Value = [M31; 16];

    fn cs(&self) -> ConstraintSystemRef {
        self.digest.cs()
    }
}

impl ChannelVar {
    pub fn default(cs: &ConstraintSystemRef) -> Self {
        let n_sent = 0;
        let digest = Poseidon2HalfStateRef::zero(cs);
        Self { n_sent, digest }
    }

    pub fn mix_root(&mut self, root: &mut HashVar) {
        let (_, right) = Poseidon2HalfStateRef::permute(root, &mut self.digest, true, false);
        self.digest = right;
        self.n_sent = 0;
    }

    pub fn get_felts(&mut self) -> [QM31Var; 2] {
        let cs = self.cs();

        let n_sent = M31Var::new_constant(&cs, &M31::from(self.n_sent as u32));
        self.n_sent += 1;

        let n_sent = QM31Var::from(&n_sent);

        let mut left = Poseidon2HalfStateRef::from_qm31(&n_sent, &QM31Var::zero(&cs));
        let (left, _) = Poseidon2HalfStateRef::permute(&mut left, &mut self.digest, false, true);
        left.to_qm31()
    }

    pub fn absorb_one_felt_and_permute(&mut self, felt: &QM31Var) {
        let cs = self.cs();
        let mut left = Poseidon2HalfStateRef::from_qm31(&felt, &QM31Var::zero(&cs));
        let (_, new_right) =
            Poseidon2HalfStateRef::permute(&mut left, &mut self.digest, true, false);

        self.digest = new_right;
        self.n_sent = 0;
    }

    pub fn absorb_two_felts_and_permute(&mut self, felt1: &QM31Var, felt2: &QM31Var) {
        let mut left = Poseidon2HalfStateRef::from_qm31(&felt1, &felt2);
        let (_, new_right) =
            Poseidon2HalfStateRef::permute(&mut left, &mut self.digest, true, false);

        self.digest = new_right;
        self.n_sent = 0;
    }
}
