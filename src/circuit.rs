use bellperson::{ConstraintSystem, SynthesisError};
use bellperson::gadgets::boolean::Boolean;
use bellperson_emulated::field_element::{EmulatedFieldElement, EmulatedFieldParams, PseudoMersennePrime};
use ff::{PrimeFieldBits, PrimeField};
use num_bigint::BigInt;

use crate::{curve::{AffinePoint, Ed25519Curve}, field::Fe25519};

struct Ed25519FpParams;

impl EmulatedFieldParams for Ed25519FpParams {
    fn num_limbs() -> usize {
        5
    }

    fn bits_per_limb() -> usize {
        51
    }

    fn modulus() -> BigInt {
        BigInt::parse_bytes(b"7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed", 16).unwrap()
    }

    fn is_modulus_pseudo_mersenne() -> bool {
        true
    }

    fn pseudo_mersenne_params() -> Option<PseudoMersennePrime> {
        Some(PseudoMersennePrime {
            e: 255,
            c: BigInt::from(19),
        })
    }
} 

type Ed25519Fp<F> = EmulatedFieldElement<F, Ed25519FpParams>;

impl<F> From<&Fe25519> for Ed25519Fp<F>
where
    F: PrimeField + PrimeFieldBits
{
    fn from(value: &Fe25519) -> Self {
        Ed25519Fp::<F>::from(&value.0)
    }
}

#[derive(Clone)]
pub struct AllocatedAffinePoint<F: PrimeField + PrimeFieldBits> {
    x: Ed25519Fp<F>,
    y: Ed25519Fp<F>,
    value: AffinePoint,
}

impl<F: PrimeField + PrimeFieldBits> AllocatedAffinePoint<F> {
    pub fn alloc_affine_point<CS>(
        cs: &mut CS,
        value: &AffinePoint,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x_limb_values = Ed25519Fp::<F>::from(&value.x);
        let y_limb_values = Ed25519Fp::<F>::from(&value.y);

        let x = x_limb_values.allocate_field_element_unchecked(&mut cs.namespace(|| "allocate x"))?;
        let y = y_limb_values.allocate_field_element_unchecked(&mut cs.namespace(|| "allocate y"))?;

        Ok(Self { x, y, value: value.clone() })
    }

    pub fn alloc_identity_point<CS>(
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let identity_value = AffinePoint::default();
        let identity = Self::alloc_affine_point(
            &mut cs.namespace(|| "alloc identity point"),
            &identity_value,
        )?;

        identity.x.assert_equality_to_constant(
            &mut cs.namespace(|| "check x equals 0"),
            &Ed25519Fp::zero(),
        )?;
        identity.y.assert_equality_to_constant(
            &mut cs.namespace(|| "check y equals 1"),
            &Ed25519Fp::one(),
        )?;
        Ok(identity)
    }


    fn verify_point_addition<CS>(
        cs: &mut CS,
        p: &Self,
        q: &Self,
        r: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x1 = &p.x;
        let y1 = &p.y;
        let x2 = &q.x;
        let y2 = &q.y;
        let x3 = &r.x;
        let y3 = &r.y;
        
        let one = Ed25519Fp::<F>::from(&Fe25519::one());
        let d = Ed25519Fp::<F>::from(&Ed25519Curve::d());

        let x1x2 = x1.mul(
            &mut cs.namespace(|| "x1*x2"),
            x2,
        )?;
        let y1y2 = y1.mul(
            &mut cs.namespace(|| "y1*y2"),
            y2,
        )?;
        let x1y2 = x1.mul(
            &mut cs.namespace(|| "x1*y2"),
            y2,
        )?;
        let x2y1 = x2.mul(
            &mut cs.namespace(|| "x2*y1"),
            y1,
        )?;

        let x1x2y1y2 = x1x2.mul(
            &mut cs.namespace(|| "x1*x2*y1*y2"),
            &y1y2,
        )?;
        let dx1x2y1y2 = d.mul(
            &mut cs.namespace(|| "d*x1*x2*y1*y2"),
            &x1x2y1y2,
        )?;

        let dx1x2y1y2_plus_1 = one.add(
            &mut cs.namespace(|| "1 + d*x1*x2*y1*y2"),
            &dx1x2y1y2
        )?;
        let neg_dx1x2y1y2_plus_1 = one.sub(
            &mut cs.namespace(|| "1 - d*x1*x2*y1*y2"),
            &dx1x2y1y2
        )?;

        let x3_times_denominator = x3.mul(
            &mut cs.namespace(|| "x3*(1 + d*x1*x2*y1*y2)"),
            &dx1x2y1y2_plus_1,
        )?;

        let x1y2_plus_x2y1 = x1y2.add(
            &mut cs.namespace(|| "x1*y2 + x1*y2"),
            &x2y1,
        )?;
        Ed25519Fp::<F>::assert_is_equal(
            &mut cs.namespace(|| "x3*(1 + d*x1*x2*y1*y2) == x1*y2 + x2*y1"),
            &x1y2_plus_x2y1,
            &x3_times_denominator,
        )?;

        let y3_times_denominator = y3.mul(
            &mut cs.namespace(|| "y3*(1 - d*x1*x2*y1*y2)"),
            &neg_dx1x2y1y2_plus_1,
        )?;

        let x1x2_plus_y1y2 = x1x2.add(
            &mut cs.namespace(|| "Reduce x1*x2 + y1*y2"),
            &y1y2,
        )?;
        Ed25519Fp::<F>::assert_is_equal(
            &mut cs.namespace(|| "y3*(1 - d*x1*x2*y1*y2) == x1*x2 + y1*y2"),
            &y3_times_denominator,
            &x1x2_plus_y1y2,
        )?;

        Ok(())
    }

    pub fn ed25519_point_addition<CS>(
        cs: &mut CS,
        p: &Self,
        q: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let sum_value = &p.value + &q.value;
        let sum = Self::alloc_affine_point(
            &mut cs.namespace(|| "allocate sum"),
            &sum_value,
        )?;

        sum.x.check_field_membership(
            &mut cs.namespace(|| "check x coordinate of sum is in base field")
        )?;
        sum.y.check_field_membership(
            &mut cs.namespace(|| "check y coordinate of sum is in base field")
        )?;

        Self::verify_point_addition(
            &mut cs.namespace(|| "verify point addition"),
            p,
            q,
            &sum,
        )?;

        Ok(sum)
    }

    fn verify_point_doubling<CS>(
        cs: &mut CS,
        p: &Self,
        doubled_p: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if !p.value.is_on_curve() {
            eprintln!("Input to this method must be a curve point");
            return Err(SynthesisError::Unsatisfiable);
        }

        let x = &p.x;
        let y = &p.y;

        let x2 = x.mul(
            &mut cs.namespace(|| "x*x"),
            x,
        )?;
        let y2 = y.mul(
            &mut cs.namespace(|| "y*y"),
            y,
        )?;
        let xy = x.mul(
            &mut cs.namespace(|| "x*y"),
            y,
        )?;

        // Numerator of doubled_p x-coordinate
        let expected_x_numerator = xy.mul_const(
            &mut cs.namespace(|| "2*x*y"),
            &BigInt::from(2),
        )?;
        let minus_x2 = x2.neg(&mut cs.namespace(|| "-x*x"))?;
        // Since curve equation is -x^2 + y^2 = 1 + dx^2y^2, we can calculate the RHS using the LHS
        let doubled_p_x_denominator = minus_x2.add(
            &mut cs.namespace(|| "-x*x+ y*y  a.k.a  1 + d*x*x*y*y"),
            &y2,
        )?;
        let doubled_p_x_numerator = doubled_p.x.mul(
            &mut cs.namespace(|| "2P.x times (1+d*x*x*y*y)"),
            &doubled_p_x_denominator,
        )?;
        Ed25519Fp::<F>::assert_is_equal(
            &mut cs.namespace(|| "2P.x times (1+d*x*x*y*y) == 2*x*y"),
            &doubled_p_x_numerator,
            &expected_x_numerator,
        )?;


        // Numerator of doubled_p y-coordinate
        let expected_y_numerator = x2.add(
            &mut cs.namespace(|| "x*x + y*y"),
            &y2,
        )?;
        let two = Ed25519Fp::<F>::from(&Fe25519::from(2u64));
        let doubled_p_y_denominator = two.sub(
            &mut cs.namespace(|| " 2 - (1 + d*x*x*y*y) = 1 - d*x*x*y*y"),
            &doubled_p_x_denominator,
        )?;
        let doubled_p_y_numerator = doubled_p.y.mul(
            &mut cs.namespace(|| "2P.y times (1-d*x*x*y*y)"),
            &doubled_p_y_denominator,
        )?;
        Ed25519Fp::<F>::assert_is_equal(
            &mut cs.namespace(|| "2P.y times (1-d*x*x*y*y) == x*x + y*y"),
            &doubled_p_y_numerator,
            &expected_y_numerator,
        )?;
        
        Ok(())
    }

    pub fn ed25519_point_doubling<CS>(
        cs: &mut CS,
        p: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let double_value = p.value.double();
        let double_p = Self::alloc_affine_point(
            &mut cs.namespace(|| "allocate 2P"),
            &double_value,
        )?;

        double_p.x.check_field_membership(
            &mut cs.namespace(|| "check x coordinate of double point is in base field")
        )?;
        double_p.y.check_field_membership(
            &mut cs.namespace(|| "check y coordinate of double point is in base field")
        )?;

        Self::verify_point_doubling(
            &mut cs.namespace(|| "verify point doubling"),
            p,
            &double_p,
        )?;

        Ok(double_p)
    }


    /// If `condition` is true, return `in1`. Otherwise, return `in0`.
    /// `selector_bits` are little-endian order
    fn conditionally_select<CS>(
        cs: &mut CS,
        inputs: &[&Self],
        selector_bits: &[Boolean],
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if inputs.len() != (1usize << selector_bits.len()) {
            eprintln!(
                "Number of inputs {} must be equal to 2^(number of selector bits) = 2^{}",
                inputs.len(),
                selector_bits.len(),
            );
            return Err(SynthesisError::Unsatisfiable);
        }
        let inputs_x = inputs
            .iter()
            .map(|i| i.x.clone())
            .collect::<Vec<_>>();
        let inputs_y = inputs
            .iter()
            .map(|i| i.y.clone())
            .collect::<Vec<_>>();

        let x = EmulatedFieldElement::mux_tree(
            &mut cs.namespace(|| "allocate value of output x coordinate"),
            selector_bits.into_iter().rev(), // mux_tree requires MSB first
            &inputs_x,
        )?;
        let y = EmulatedFieldElement::mux_tree(
            &mut cs.namespace(|| "allocate value of output y coordinate"),
            selector_bits.into_iter().rev(), // mux_tree requires MSB first
            &inputs_y,
        )?;

        let mut res_index = 0usize;
        for (i, b) in selector_bits.iter().enumerate() {
            if b.get_value().unwrap() {
                res_index += 1 << i;
            }
        }
        let value = inputs[res_index].value.clone();
        
        Ok(Self { x, y, value })
    }

    pub fn ed25519_scalar_multiplication_window1<CS>(
        &self,
        cs: &mut CS,
        scalar: Vec<Boolean>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if scalar.len() >= 254usize {
            // the largest curve25519 scalar fits in 253 bits
            eprintln!("Scalar bit vector has more than 253 bits");
            return Err(SynthesisError::Unsatisfiable);
        }
        
        // No range checks on limbs required as it is checked to be equal to (0,1)
        let mut output = Self::alloc_identity_point(
            &mut cs.namespace(|| "allocate initial value of output"),
        )?;

        // Remember to avoid field membership checks before calling this function
        self.x.check_field_membership(
            &mut cs.namespace(|| "check x coordinate of base point is in base field")
        )?;
        self.y.check_field_membership(
            &mut cs.namespace(|| "check y coordinate of base point is in base field")
        )?;

        let mut step_point = self.clone();

        for (i, bit) in scalar.into_iter().enumerate() {
            let output0 = output.clone();
            let output1 = Self::ed25519_point_addition(
                &mut cs.namespace(|| format!("sum in step {i} if bit is one")),
                &output,
                &step_point,
            )?;

            output = Self::conditionally_select(
                &mut cs.namespace(|| format!("conditionally select output point in step {i}")),
                &[&output0, &output1],
                &[bit],
            )?;

            step_point = Self::ed25519_point_doubling(
                &mut cs.namespace(|| format!("point doubling in step {i}")),
                &step_point,
            )?;
        }

        Ok(output)
    }
    
    pub fn ed25519_scalar_multiplication_window2<CS>(
        &self,
        cs: &mut CS,
        scalar: Vec<Boolean>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if scalar.len() >= 254usize {
            // the largest curve25519 scalar fits in 253 bits
            eprintln!("Scalar bit vector has more than 253 bits");
            return Err(SynthesisError::Unsatisfiable);
        }
        
        // No range checks on limbs required as it is checked to be equal to (0,1)
        let identity_point = Self::alloc_identity_point(
            &mut cs.namespace(|| "allocate identity point"),
        )?;

        // Remember to avoid field membership checks before calling this function
        self.x.check_field_membership(
            &mut cs.namespace(|| "check x coordinate of base point is in base field")
        )?;
        self.y.check_field_membership(
            &mut cs.namespace(|| "check y coordinate of base point is in base field")
        )?;

        let self_times_2 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate double the base"),
            self,
        )?;
        let self_times_3 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate three times the base"),
            &self_times_2,
            self,
        )?;
        let n = scalar.len() - 1;
        assert!(n > 0);

        let mut output = Self::conditionally_select(
            &mut cs.namespace(|| "allocate initial value of output"),
            &[&identity_point, self, &self_times_2, &self_times_3],
            &[scalar[n-1].clone(), scalar[n].clone()],
        )?;
            
        let mut i = n-2;
        while i > 0 {
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| format!("first doubling in iteration {i}")),
                &output,
            )?;
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| format!("second doubling in iteration {i}")),
                &output,
            )?;

            let tmp = Self::conditionally_select(
                &mut cs.namespace(|| format!("allocate tmp value in iteration {i}")),
                &[&identity_point, self, &self_times_2, &self_times_3],
                &[scalar[i-1].clone(), scalar[i].clone()],
            )?;

            output = Self::ed25519_point_addition(
                &mut cs.namespace(|| format!("allocate sum of output and tmp in iteration {i}")),
                &output,
                &tmp,
            )?;
                
            i = i-2;
        }

        if scalar.len() % 2 == 1 {
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| "final doubling of output"),
                &output,
            )?;
            let tmp = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of output and base"),
                &output,
                &self,
            )?;
            output = Self::conditionally_select(
                cs,
                &[&output, &tmp],
                &[scalar[0].clone()],
            )?;
            
        }

        Ok(output)
    }

    pub fn ed25519_scalar_multiplication_window3<CS>(
        &self,
        cs: &mut CS,
        scalar: Vec<Boolean>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if scalar.len() >= 254usize {
            // the largest curve25519 scalar fits in 253 bits
            eprintln!("Scalar bit vector has more than 253 bits");
            return Err(SynthesisError::Unsatisfiable);
        }
        
        // No range checks on limbs required as it is checked to be equal to (0,1)
        let identity_point = Self::alloc_identity_point(
            &mut cs.namespace(|| "allocate identity point"),
        )?;

        // Remember to avoid field membership checks before calling this function
        self.x.check_field_membership(
            &mut cs.namespace(|| "check x coordinate of base point is in base field")
        )?;
        self.y.check_field_membership(
            &mut cs.namespace(|| "check y coordinate of base point is in base field")
        )?;

        let self_times_2 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate double the base"),
            self,
        )?;
        let self_times_3 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate three times the base"),
            &self_times_2,
            self,
        )?;
        let self_times_4 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate four times the base"),
            &self_times_2,
        )?;
        let self_times_5 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate five times the base"),
            &self_times_4,
            self,
        )?;
        let self_times_6 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate six times the base"),
            &self_times_3,
        )?;
        let self_times_7 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate seven times the base"),
            &self_times_6,
            self,
        )?;
        let n = scalar.len() - 1;
        assert!(n > 1);

        let mut output = Self::conditionally_select(
            &mut cs.namespace(|| "allocate initial value of output"),
            &[&identity_point, self, &self_times_2, &self_times_3, &self_times_4, &self_times_5, &self_times_6, &self_times_7],
            &[scalar[n-2].clone(), scalar[n-1].clone(), scalar[n].clone()]
        )?;
            
        let mut i = n-3;
        while i > 1 {
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| format!("first doubling in iteration {i}")),
                &output,
            )?;
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| format!("second doubling in iteration {i}")),
                &output,
            )?;
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| format!("third doubling in iteration {i}")),
                &output,
            )?;

            let tmp = Self::conditionally_select(
                &mut cs.namespace(|| format!("allocate tmp value in iteration {i}")),
                &[&identity_point, self, &self_times_2, &self_times_3, &self_times_4, &self_times_5, &self_times_6, &self_times_7],
                &[scalar[i-2].clone(), scalar[i-1].clone(), scalar[i].clone()]
            )?;

            output = Self::ed25519_point_addition(
                &mut cs.namespace(|| format!("allocate sum of output and tmp in iteration {i}")),
                &output,
                &tmp,
            )?;
                
            i = i-3;
        }

        if scalar.len() % 3 == 1 {
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| "final doubling of output"),
                &output,
            )?;
            let tmp = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of output and base"),
                &output,
                &self,
            )?;
            output = Self::conditionally_select(
                cs,
                &[&output, &tmp],
                &[scalar[0].clone()],
            )?;
        } else if scalar.len() % 3 == 2 {
            let output2 = Self::ed25519_point_doubling(
                &mut cs.namespace(|| "final doubling of output"),
                &output,
            )?;
            let output4 = Self::ed25519_point_doubling(
                &mut cs.namespace(|| "final quadrupling of output"),
                &output2,
            )?;
            let tmp1 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 4*output and base"),
                &output4,
                &self,
            )?;
            let tmp2 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 4*output and 2*base"),
                &output4,
                &self_times_2,
            )?;
            let tmp3 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 4*output and 3*base"),
                &output4,
                &self_times_3,
            )?;
            output = Self::conditionally_select(
                cs,
                &[&output4, &tmp1, &tmp2, &tmp3],
                &[scalar[0].clone(), scalar[1].clone()],
            )?;
        }

        Ok(output)
    }

     pub fn ed25519_scalar_multiplication_window4<CS>(
        &self,
        cs: &mut CS,
        scalar: Vec<Boolean>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if scalar.len() >= 254usize {
            // the largest curve25519 scalar fits in 253 bits
            eprintln!("Scalar bit vector has more than 253 bits");
            return Err(SynthesisError::Unsatisfiable);
        }
        
        // No range checks on limbs required as it is checked to be equal to (0,1)
        let identity_point = Self::alloc_identity_point(
            &mut cs.namespace(|| "allocate identity point"),
        )?;

        // Remember to avoid field membership checks before calling this function
        self.x.check_field_membership(
            &mut cs.namespace(|| "check x coordinate of base point is in base field")
        )?;
        self.y.check_field_membership(
            &mut cs.namespace(|| "check y coordinate of base point is in base field")
        )?;

        let self_times_2 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate double the base"),
            self,
        )?;
        let self_times_3 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate three times the base"),
            &self_times_2,
            self,
        )?;
        let self_times_4 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate four times the base"),
            &self_times_2,
        )?;
        let self_times_5 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate five times the base"),
            &self_times_4,
            self,
        )?;
        let self_times_6 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate six times the base"),
            &self_times_3,
        )?;
        let self_times_7 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate seven times the base"),
            &self_times_6,
            self,
        )?;
        let self_times_8 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate eight times the base"),
            &self_times_4,
        )?;
        let self_times_9 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate nine times the base"),
            &self_times_8,
            self,
        )?;
        let self_times_10 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate ten times the base"),
            &self_times_5,
        )?;
        let self_times_11 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate eleven times the base"),
            &self_times_10,
            self,
        )?;
        let self_times_12 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate twelve times the base"),
            &self_times_6,
        )?;
        let self_times_13 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate thirteen times the base"),
            &self_times_12,
            self,
        )?;
        let self_times_14 = Self::ed25519_point_doubling(
            &mut cs.namespace(|| "allocate fourteen times the base"),
            &self_times_7,
        )?;
        let self_times_15 = Self::ed25519_point_addition(
            &mut cs.namespace(|| "allocate fifteen times the base"),
            &self_times_14,
            self,
        )?;
        let n = scalar.len() - 1;
        assert!(n > 2);

        let mut output = Self::conditionally_select(
            &mut cs.namespace(|| "allocate initial value of output"),
            &[
                &identity_point, self, &self_times_2, &self_times_3, &self_times_4, &self_times_5, &self_times_6, &self_times_7,
                &self_times_8, &self_times_9, &self_times_10, &self_times_11, &self_times_12, &self_times_13, &self_times_14, &self_times_15,
            ],
            &[scalar[n-3].clone(), scalar[n-2].clone(), scalar[n-1].clone(), scalar[n].clone()]
        )?;
            
        let mut i = n-4;
        while i > 2 {
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| format!("first doubling in iteration {i}")),
                &output,
            )?;
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| format!("second doubling in iteration {i}")),
                &output,
            )?;
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| format!("third doubling in iteration {i}")),
                &output,
            )?;
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| format!("fourth doubling in iteration {i}")),
                &output,
            )?;

            let tmp = Self::conditionally_select(
                &mut cs.namespace(|| format!("allocate tmp value in iteration {i}")),
                &[
                    &identity_point, self, &self_times_2, &self_times_3, &self_times_4, &self_times_5, &self_times_6, &self_times_7,
                    &self_times_8, &self_times_9, &self_times_10, &self_times_11, &self_times_12, &self_times_13, &self_times_14, &self_times_15,
                ],
                &[scalar[i-3].clone(), scalar[i-2].clone(), scalar[i-1].clone(), scalar[i].clone()]
            )?;

            output = Self::ed25519_point_addition(
                &mut cs.namespace(|| format!("allocate sum of output and tmp in iteration {i}")),
                &output,
                &tmp,
            )?;
                
            i = i-4;
        }

        if scalar.len() % 4 == 1 {
            output = Self::ed25519_point_doubling(
                &mut cs.namespace(|| "final doubling of output"),
                &output,
            )?;
            let tmp = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of output and base"),
                &output,
                &self,
            )?;
            output = Self::conditionally_select(
                cs,
                &[&output, &tmp],
                &[scalar[0].clone()],
            )?;
        } else if scalar.len() % 4 == 2 {
            let output2 = Self::ed25519_point_doubling(
                &mut cs.namespace(|| "final doubling of output"),
                &output,
            )?;
            let output4 = Self::ed25519_point_doubling(
                &mut cs.namespace(|| "final quadrupling of output"),
                &output2,
            )?;
            let tmp1 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 4*output and base"),
                &output4,
                &self,
            )?;
            let tmp2 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 4*output and 2*base"),
                &output4,
                &self_times_2,
            )?;
            let tmp3 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 4*output and 3*base"),
                &output4,
                &self_times_3,
            )?;
            output = Self::conditionally_select(
                cs,
                &[&output4, &tmp1, &tmp2, &tmp3],
                &[scalar[0].clone(), scalar[1].clone()],
            )?;
        } else if scalar.len() % 4 == 3 {
            let output2 = Self::ed25519_point_doubling(
                &mut cs.namespace(|| "final doubling of output"),
                &output,
            )?;
            let output4 = Self::ed25519_point_doubling(
                &mut cs.namespace(|| "final quadrupling of output"),
                &output2,
            )?;
            let output8 = Self::ed25519_point_doubling(
                &mut cs.namespace(|| "final octupling of output"),
                &output4,
            )?;
            let tmp1 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 8*output and base"),
                &output8,
                &self,
            )?;
            let tmp2 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 8*output and 2*base"),
                &output8,
                &self_times_2,
            )?;
            let tmp3 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 8*output and 3*base"),
                &output8,
                &self_times_3,
            )?;
            let tmp4 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 8*output and 4*base"),
                &output8,
                &self_times_4,
            )?;
            let tmp5 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 8*output and 5*base"),
                &output8,
                &self_times_5,
            )?;
            let tmp6 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 8*output and 6*base"),
                &output8,
                &self_times_6,
            )?;
            let tmp7 = Self::ed25519_point_addition(
                &mut cs.namespace(|| "final sum of 8*output and 7*base"),
                &output8,
                &self_times_7,
            )?;
            output = Self::conditionally_select(
                cs,
                &[&output8, &tmp1, &tmp2, &tmp3, &tmp4, &tmp5, &tmp6, &tmp7],
                &[scalar[0].clone(), scalar[1].clone(), scalar[2].clone()],
            )?;
        }

        Ok(output)
    }
}


#[cfg(test)]
mod tests {
    use crate::curve::Ed25519Curve;

    use super::*;
    use bellperson::gadgets::test::TestConstraintSystem;
    use num_bigint::{RandBigInt, BigUint};
    use num_integer::Integer;
    use num_traits::Zero;
    use pasta_curves::Fp;

    #[test]
    fn alloc_affine_point_addition() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();
        let scalar = rng.gen_biguint_range(&BigUint::zero(), &Ed25519Curve::order());
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);
        let scalar = rng.gen_biguint_range(&BigUint::zero(), &Ed25519Curve::order());
        let q = Ed25519Curve::scalar_multiplication(&b, &scalar);
        let sum_expected_value = &p + &q;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let p_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "alloc point p"),
            &p,
        );
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        let q_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "alloc point q"),
            &q,
        );
        assert!(q_alloc.is_ok());
        let q_al = q_alloc.unwrap();

        let sum_alloc = AllocatedAffinePoint::ed25519_point_addition(
            &mut cs.namespace(|| "adding p and q"),
            &p_al,
            &q_al,
        );
        assert!(sum_alloc.is_ok());
        let sum_al = sum_alloc.unwrap();

        assert_eq!(sum_expected_value, sum_al.value);

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_affine_point_doubling() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();
        let scalar = rng.gen_biguint_range(&BigUint::zero(), &Ed25519Curve::order());
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);
        let double_expected_value = p.double();

        let mut cs = TestConstraintSystem::<Fp>::new();

        let p_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "alloc point p"),
            &p,
        );
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        let double_alloc = AllocatedAffinePoint::ed25519_point_doubling(
            &mut cs.namespace(|| "doubling p"),
            &p_al,
        );
        assert!(double_alloc.is_ok());
        let double_al = double_alloc.unwrap();

        assert_eq!(double_expected_value, double_al.value);

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_affine_scalar_multiplication_window1() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();
       
        let mut scalar = rng.gen_biguint(256u64);
        scalar = scalar >> 3; // scalar now has 253 significant bits
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);
       
        let mut scalar_vec: Vec<Boolean> = vec![];
        for _i in 0..253 {
            if scalar.is_odd() {
                scalar_vec.push(Boolean::constant(true))
            } else {
                scalar_vec.push(Boolean::constant(false))
            };
            scalar = scalar >> 1;
        }

        let mut cs = TestConstraintSystem::<Fp>::new();

        let b_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "allocate base point"),
            &b,
        );
        assert!(b_alloc.is_ok());
        let b_al = b_alloc.unwrap();

        let p_alloc = b_al.ed25519_scalar_multiplication_window1(
            &mut cs.namespace(|| "scalar multiplication"),
            scalar_vec,
        );
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        assert_eq!(p, p_al.value);

        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_affine_scalar_multiplication_window2() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();
       
        let mut scalar = rng.gen_biguint(256u64);
        scalar = scalar >> 3; // scalar now has 253 significant bits
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);
       
        let mut scalar_vec: Vec<Boolean> = vec![];
        for _i in 0..253 {
            if scalar.is_odd() {
                scalar_vec.push(Boolean::constant(true))
            } else {
                scalar_vec.push(Boolean::constant(false))
            };
            scalar = scalar >> 1;
        }

        let mut cs = TestConstraintSystem::<Fp>::new();

        let b_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "allocate base point"),
            &b,
        );
        assert!(b_alloc.is_ok());
        let b_al = b_alloc.unwrap();

        let p_alloc = b_al.ed25519_scalar_multiplication_window2(
            &mut cs.namespace(|| "scalar multiplication"),
            scalar_vec,
        );
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        assert_eq!(p, p_al.value);

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_affine_scalar_multiplication_window3() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();
       
        let mut scalar = rng.gen_biguint(256u64);
        scalar = scalar >> 3; // scalar now has 253 significant bits
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);
       
        let mut scalar_vec: Vec<Boolean> = vec![];
        for _i in 0..253 {
            if scalar.is_odd() {
                scalar_vec.push(Boolean::constant(true))
            } else {
                scalar_vec.push(Boolean::constant(false))
            };
            scalar = scalar >> 1;
        }

        let mut cs = TestConstraintSystem::<Fp>::new();

        let b_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "allocate base point"),
            &b,
        );
        assert!(b_alloc.is_ok());
        let b_al = b_alloc.unwrap();

        let p_alloc = b_al.ed25519_scalar_multiplication_window3(
            &mut cs.namespace(|| "scalar multiplication"),
            scalar_vec,
        );
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        assert_eq!(p, p_al.value);

        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_affine_scalar_multiplication_window4() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();
       
        let mut scalar = rng.gen_biguint(256u64);
        scalar = scalar >> 3; // scalar now has 253 significant bits
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);
       
        let mut scalar_vec: Vec<Boolean> = vec![];
        for _i in 0..253 {
            if scalar.is_odd() {
                scalar_vec.push(Boolean::constant(true))
            } else {
                scalar_vec.push(Boolean::constant(false))
            };
            scalar = scalar >> 1;
        }

        let mut cs = TestConstraintSystem::<Fp>::new();

        let b_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "allocate base point"),
            &b,
        );
        assert!(b_alloc.is_ok());
        let b_al = b_alloc.unwrap();

        let p_alloc = b_al.ed25519_scalar_multiplication_window4(
            &mut cs.namespace(|| "scalar multiplication"),
            scalar_vec,
        );
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        assert_eq!(p, p_al.value);

        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

}