use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_poseidon31::Poseidon2State;
use num_traits::Zero;
use stwo_prover::core::fields::m31::M31;

#[derive(Clone)]
pub struct HashVar {
    pub cs: ConstraintSystemRef,
    pub value: [M31; 8],
    pub variables: usize,
}

impl DVar for HashVar {
    type Value = [M31; 8];

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for HashVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        Self {
            cs: cs.clone(),
            value: value.clone(),
            variables: cs.new_variables(value, mode),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ChannelVar(pub Poseidon2State);

impl DVar for ChannelVar {
    type Value = <Poseidon2State as DVar>::Value;

    fn cs(&self) -> ConstraintSystemRef {
        self.0.cs()
    }
}

impl ChannelVar {
    pub fn default(cs: &ConstraintSystemRef) -> Self {
        Self(Poseidon2State::new_constant(
            cs,
            &[
                M31::zero(),
                M31::zero(),
                M31::zero(),
                M31::zero(),
                M31::zero(),
                M31::zero(),
                M31::zero(),
                M31::zero(),
                M31::from(653561903u32),
                M31::from(1570384735u32),
                M31::from(1642608663u32),
                M31::from(717067276u32),
                M31::from(1210045490u32),
                M31::from(80872923u32),
                M31::from(982214479u32),
                M31::from(945961255u32),
            ],
        ))
    }

    pub fn mix_root(&mut self, root: &HashVar) {
        let cs = self.cs().and(&root.cs());
        let value = [
            root.value[0],
            root.value[1],
            root.value[2],
            root.value[3],
            root.value[4],
            root.value[5],
            root.value[6],
            root.value[7],
            self.0.value[8],
            self.0.value[9],
            self.0.value[10],
            self.0.value[11],
            self.0.value[12],
            self.0.value[13],
            self.0.value[14],
            self.0.value[15],
        ];
        let variables = cs.copy(root.variables);
        for i in 1..8 {
            let _ = cs.copy(root.variables + i);
        }
        for i in 0..8 {
            let _ = cs.copy(self.0.variables + 8 + i);
        }

        let state = Poseidon2State {
            cs,
            value,
            variables,
        };
        self.0 = state.permute();
    }

    pub fn get_felts(&self) -> [QM31Var; 2] {
        let m31 = self.to_m31();
        [
            QM31Var::from_m31(&m31[0], &m31[1], &m31[2], &m31[3]),
            QM31Var::from_m31(&m31[4], &m31[5], &m31[6], &m31[7]),
        ]
    }

    pub fn squeeze_again(&mut self) {
        let cs = self.cs();
        let zero = M31::zero();
        let value = [
            zero,
            zero,
            zero,
            zero,
            zero,
            zero,
            zero,
            zero,
            self.0.value[8],
            self.0.value[9],
            self.0.value[10],
            self.0.value[11],
            self.0.value[12],
            self.0.value[13],
            self.0.value[14],
            self.0.value[15],
        ];

        let variables = cs.copy(0);
        for _ in 1..8 {
            cs.copy(0);
        }
        for i in 0..8 {
            cs.copy(self.0.variables + 8 + i);
        }

        let state = Poseidon2State {
            cs,
            value,
            variables,
        };
        self.0 = state.permute();
    }

    pub fn absorb_one_felt_and_permute(&mut self, felt: &QM31Var) {
        let cs = self.cs();
        let zero = M31::zero();
        let value = [
            felt.value[0],
            felt.value[1],
            felt.value[2],
            felt.value[3],
            zero,
            zero,
            zero,
            zero,
            self.0.value[8],
            self.0.value[9],
            self.0.value[10],
            self.0.value[11],
            self.0.value[12],
            self.0.value[13],
            self.0.value[14],
            self.0.value[15],
        ];

        let variables = cs.copy(felt.first.real.variable);
        cs.copy(felt.first.imag.variable);
        cs.copy(felt.second.real.variable);
        cs.copy(felt.second.imag.variable);

        cs.copy(0);
        cs.copy(0);
        cs.copy(0);
        cs.copy(0);

        for i in 0..8 {
            cs.copy(self.0.variables + 8 + i);
        }

        let state = Poseidon2State {
            cs,
            value,
            variables,
        };
        self.0 = state.permute();
    }

    pub fn absorb_two_felts_and_permute(&mut self, felt1: &QM31Var, felt2: &QM31Var) {
        let cs = self.cs();
        let value = [
            felt1.value[0],
            felt1.value[1],
            felt1.value[2],
            felt1.value[3],
            felt2.value[0],
            felt2.value[1],
            felt2.value[2],
            felt2.value[3],
            self.0.value[8],
            self.0.value[9],
            self.0.value[10],
            self.0.value[11],
            self.0.value[12],
            self.0.value[13],
            self.0.value[14],
            self.0.value[15],
        ];

        let variables = cs.copy(felt1.first.real.variable);
        cs.copy(felt1.first.imag.variable);
        cs.copy(felt1.second.real.variable);
        cs.copy(felt1.second.imag.variable);

        cs.copy(felt2.first.real.variable);
        cs.copy(felt2.first.imag.variable);
        cs.copy(felt2.second.real.variable);
        cs.copy(felt2.second.imag.variable);

        for i in 0..8 {
            cs.copy(self.0.variables + 8 + i);
        }

        let state = Poseidon2State {
            cs,
            value,
            variables,
        };
        self.0 = state.permute();
    }
}
