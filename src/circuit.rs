use bellperson::{ConstraintSystem, SynthesisError};
use bellperson_emulated::field_element::{EmulatedFieldElement, EmulatedFieldParams};
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

        let x = x_limb_values.allocate_field_element(&mut cs.namespace(|| "allocate x"))?;
        let y = y_limb_values.allocate_field_element(&mut cs.namespace(|| "allocate y"))?;

        Ok(Self { x, y, value: value.clone() })
    }


    fn verify_ed25519_point_addition<CS>(
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

        // sum.x.check_base_field_membership(
        //     &mut cs.namespace(|| "check x coordinate of sum is in base field")
        // )?;
        // sum.y.check_base_field_membership(
        //     &mut cs.namespace(|| "check y coordinate of sum is in base field")
        // )?;

        Self::verify_ed25519_point_addition(
            &mut cs.namespace(|| "verify point addition"),
            p,
            q,
            &sum,
        )?;

        Ok(sum)
    }
}


#[cfg(test)]
mod tests {
    use crate::curve::Ed25519Curve;

    use super::*;
    use bellperson::gadgets::test::TestConstraintSystem;
    use num_bigint::RandBigInt;
    use num_traits::Zero;
    use pasta_curves::Fp;

    #[test]
    fn alloc_affine_point_addition_verification() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();
        let scalar = rng.gen_bigint_range(&BigInt::zero(), &Ed25519Curve::order());
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);
        let scalar = rng.gen_bigint_range(&BigInt::zero(), &Ed25519Curve::order());
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

}