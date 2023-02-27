use std::marker::PhantomData;

use halo2_proofs::{
    circuit::*,
    plonk::*, poly::Rotation, pasta::Fp, arithmetic::Field, dev::MockProver,
};

#[derive(Debug, Clone)]
struct ArraySumConfig {
    pub advice: [Column<Advice>; 3],
    pub selector: Selector,
    pub instance: Column<Instance>,
}

struct FiboChip<F: Field, const N: usize> {
    config: ArraySumConfig,
    _marker: PhantomData<F>,
}

impl<F: Field, const N: usize> FiboChip<F, N> {
    fn construct(config: ArraySumConfig) -> Self {
        Self { config, _marker: PhantomData }
    }

    fn configure(meta: &mut ConstraintSystem<F>, advice: [Column<Advice>; 3], instance: Column<Instance>, constant: Column<Fixed>) -> ArraySumConfig {
        // We receive the advices as args so we can reuse them
        let [col_a, col_b, col_accum] = advice;

        // Selectors do get optimized by the backend, so no need to receive them as args
        let selector: Selector = meta.selector();

        // Needed to use permutation argument
        meta.enable_equality(instance);
        meta.enable_constant(constant);
        for column in &advice {
            meta.enable_equality(*column);
        }

        // Create a custom gate for addition. There are no pre-built gates in Halo2.
        meta.create_gate("add", |meta| {
            let s = meta.query_selector(selector);
            
            // Rotation lets us pick the current row, or a row given an offset
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c  = meta.query_advice(col_accum, Rotation::cur());
            
            // If selector s is set, then a+b=c
            vec![s * (a + b - c)]
        });

        ArraySumConfig { advice: [col_a,col_b,col_accum], selector, instance }
    }

    fn assign_row(&self, mut layouter: impl Layouter<F>,  xs: [Value<F>; N]) -> Result<AssignedCell<F,F>, Error>  {        
        layouter.assign_region(
            || "next row",
            |mut region| {
                let [col_a, col_x, col_accum] = self.config.advice;
                self.config.selector.enable(&mut region, 0)?;
                let mut out_cell = Err(Error::Synthesis);
                let mut accum_value: Value<F> = Value::known(F::ZERO);
                
                for row in 0..N {
                    let x = xs[row];
                    self.config.selector.enable(&mut region, row)?;
                    
                    region.assign_advice(
                        || "a", 
                        col_a, 
                        row, 
                        || accum_value
                    )?;

                    region.assign_advice(
                        || format!("x[{}]", row),
                        col_x,
                        row,
                        || x
                    )?;

                    accum_value = accum_value + x;
                    out_cell = region.assign_advice(
                        || format!("out[{}]", row),
                        col_accum,
                        row,
                        || accum_value
                    );
                };

                out_cell
            }
        )
    }

    pub fn expose_public(&self, mut layouter: impl Layouter<F>, cell: &AssignedCell<F, F>, row: usize) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }

}


struct ArraySumCircuit<F: Field, const N: usize> {
    xs: [Value<F>; N],
}

impl<F: Field, const N: usize> Circuit<F> for ArraySumCircuit<F, N> {
    type Config = ArraySumConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            xs: [Value::unknown(); N],     
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let instance = meta.instance_column();
        let constant = meta.fixed_column();

        FiboChip::<F, N>::configure(meta, [col_a, col_b, col_c], instance, constant)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = FiboChip::construct(config);
        
        // Assign returns the last row from col_accum that contains the total accumulated score, 
        // which we expose by matching it to the public instance that corresponds to round N-1
        let out_cell = chip.assign_row(layouter.namespace(|| "rps"), self.xs)?;        
        chip.expose_public(layouter.namespace(|| "out"), &out_cell, N-1)?;
        
        Ok(())
    }
}

// Returns the circuit configured with the private inputs, and the public inputs
fn make_circuit<const N: usize>(xs: [u64; N], out: u64) -> (ArraySumCircuit<Fp, N>, Vec<Vec<Fp>>) {
    // The plays in each round are the private inputs to the circuit
    let circuit = ArraySumCircuit {
        xs: xs.map(|val| Value::known(Fp::from(val))),
    };

    // We can fill the public instances with zeros up until the last score,
    // since we only care about the total accumulated at the end of all rounds
    let mut outs = vec![Fp::zero(); N];
    outs[N-1] = Fp::from(out);

    (circuit, vec![outs])
}
 

#[test]
fn test_01() {
    let k = 4;

    let xs = [1, 2, 3, 10];
    let out = 16;

    let (circuit, public_input) = make_circuit(xs, out);

    let prover = MockProver::run(k, &circuit, public_input).unwrap();
    prover.assert_satisfied();
    println!("success!")
}