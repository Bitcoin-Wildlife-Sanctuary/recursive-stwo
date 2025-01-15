use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_poseidon31::Poseidon2HalfStateRef;
use num_traits::Zero;
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

    pub fn mix_root(&mut self, root: &HashVar) {
        let (_, right) = Poseidon2HalfStateRef::permute(root, &self.digest);
        self.digest = right;
        self.n_sent = 0;
    }

    pub fn get_felts(&mut self) -> [QM31Var; 2] {
        let cs = self.cs();

        let n_sent = M31Var::new_constant(&cs, &M31::from(self.n_sent as u32));
        self.n_sent += 1;

        let half_state_variable = cs.copy(n_sent.variable);
        cs.copy(0);
        cs.copy(0);
        cs.copy(0);
        cs.copy(0);
        cs.copy(0);
        cs.copy(0);
        cs.copy(0);

        let zero = M31::zero();
        let left = Poseidon2HalfStateRef {
            cs: cs.clone(),
            value: [n_sent.value, zero, zero, zero, zero, zero, zero, zero],
            half_state_variable,
            addr_variable: cs
                .new_variables(&[M31::from(half_state_variable)], AllocationMode::Constant),
        };

        let (left, _) = Poseidon2HalfStateRef::permute(&left, &self.digest);

        let m31 = left.to_m31();
        [
            QM31Var::from_m31(&m31[0], &m31[1], &m31[2], &m31[3]),
            QM31Var::from_m31(&m31[4], &m31[5], &m31[6], &m31[7]),
        ]
    }

    pub fn absorb_one_felt_and_permute(&mut self, felt: &QM31Var) {
        let cs = self.cs();

        let half_state_variable = cs.copy(felt.first.real.variable);
        cs.copy(felt.first.imag.variable);
        cs.copy(felt.second.real.variable);
        cs.copy(felt.second.imag.variable);
        cs.copy(0);
        cs.copy(0);
        cs.copy(0);
        cs.copy(0);

        let zero = M31::zero();
        let left = Poseidon2HalfStateRef {
            cs: cs.clone(),
            value: [
                felt.value.0 .0,
                felt.value.0 .1,
                felt.value.1 .0,
                felt.value.1 .1,
                zero,
                zero,
                zero,
                zero,
            ],
            half_state_variable,
            addr_variable: cs
                .new_variables(&[M31::from(half_state_variable)], AllocationMode::Constant),
        };

        let (_, new_right) = Poseidon2HalfStateRef::permute(&left, &self.digest);

        self.digest = new_right;
        self.n_sent = 0;
    }

    pub fn absorb_two_felts_and_permute(&mut self, felt1: &QM31Var, felt2: &QM31Var) {
        let cs = self.cs();

        let half_state_variable = cs.copy(felt1.first.real.variable);
        cs.copy(felt1.first.imag.variable);
        cs.copy(felt1.second.real.variable);
        cs.copy(felt1.second.imag.variable);
        cs.copy(felt2.first.real.variable);
        cs.copy(felt2.first.imag.variable);
        cs.copy(felt2.second.real.variable);
        cs.copy(felt2.second.imag.variable);

        let left = Poseidon2HalfStateRef {
            cs: cs.clone(),
            value: [
                felt1.value.0 .0,
                felt1.value.0 .1,
                felt1.value.1 .0,
                felt1.value.1 .1,
                felt2.value.0 .0,
                felt2.value.0 .1,
                felt2.value.1 .0,
                felt2.value.1 .1,
            ],
            half_state_variable,
            addr_variable: cs
                .new_variables(&[M31::from(half_state_variable)], AllocationMode::Constant),
        };

        let (_, new_right) = Poseidon2HalfStateRef::permute(&left, &self.digest);

        self.digest = new_right;
        self.n_sent = 0;
    }
}
