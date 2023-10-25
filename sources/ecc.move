

module 0x1::ecc {

    use std::option;
    use std::option::Option;
    use aptos_std::aptos_hash;
    use aptos_std::debug::print;
    use movefuns::math::pow;
    #[test_only]
    use std::option::some;

    struct Curve has drop {
        p: u256,
        a: u256,
        b: u256,
        n: u256,
        generator: Point,
    }

    struct Point has drop, copy {
        x: u256,
        y: u256,
    }

    fun create_curve(p: u256, a: u256, b: u256, n: u256, generator: Point): Curve {
        Curve {
            p,
            a,
            b,
            n,
            generator,
        }
    }

    fun create_point(x: u256, y: u256): Point {
        Point {
            x, y
        }
    }
    // Prime field multiplication: return a*b mod p
    fun field_mul(curve: &Curve, a: u256, b: u256) : u256 {
        return (a * b) % curve.p

    }

    // Prime field division: return num/den mod p
    fun field_div(curve: &Curve, num: u256, den: u256) : u256 {
        let inverse_den = inverse_mod(den % curve.p, curve.p);
        let inverse_den = option::borrow(&inverse_den);
        field_mul(curve, num % curve.p, *inverse_den)
    }

    // Prime field exponentiation: raise num to power mod p
    fun field_exp(curve: &Curve, num: u256, power: u256) : u64 {
        return ((pow_mod(num % curve.p, power,option::some(curve.p))) as u64)
    }


    // Return the special identity point
    // We pick x=p, y=0
    fun identity(curve: &Curve): Point {
        Point {
            x: curve.p,
            y: 0,
        }
    }

    // Return the slope of the tangent of this curve at point Q
    fun tangent(curve: &Curve, q: Point): u256 {
        print(&q.x);
        let num = q.x * q.x * 3 + curve.a;
        let den = q.y*2;
        return field_div(curve, num,den)
    }


    fun add(curve: &Curve, q1: Point, q2: Point) : Point {
        // Identity special cases
        if (q1.x ==  curve.p) {
            // Q1 is identity
            return q2
        };

        if (q2.x == curve.p) {
            // Q2 is identity
            return q1
        };

        // Equality special cases
        if (q1.x == q2.x) {
            if (q1.y == q2.y) {
                return double(curve, q1)
            }
            else {
                return identity(curve)
            }
        };

        // Ordinary case
        let m = field_div(curve, q1.y + curve.p - q2.y,q1.x + curve.p - q2.x);

        line_intersect(curve, q1, q2, m)
    }

    fun double(curve: &Curve, q: Point): Point {
        if (q.x == curve.p) {
            q
        } else {
            line_intersect(curve, q, q,tangent(curve, q))
        }
    }

    fun mul(curve: &Curve, q: Point, m: u64): Point {
        let r = identity(curve);
        while (m != 0) {
            if (m&1 == 1) {
                r = add(curve, r, q);
            };
            m = m >> 1;
            if (m != 0) {
                q = double(curve, q);
            }
        };

        r
    }

    fun line_intersect(curve: &Curve, q1: Point, q2: Point, m: u256): Point {
        let v = (q1.y + curve.p - (m*q1.x)%curve.p)%curve.p;
        let x=(m*m + curve.p-q1.x + curve.p-q2.x)%curve.p;
        let y=(curve.p-(m*x)%curve.p + curve.p-v)%curve.p;
        return Point {
            x, y
        }
    }

    fun div_mod(x: u256, y: u256): (u256, u256) {
        let quotient = x / y;
        let remainder = x % y;
        return (quotient, remainder)
    }


    fun abs(left: u256, right: u256) : u256 {
        if (left < right) {
            right - left
        } else {
            left - right
        }
    }

    fun mod_calc(u: u256, q: u256, v: u256, m: u256) : u256 {
        if (q * v > u) {
            let (_, r) = div_mod(abs(u, q * v), m);
            m - r
        } else {
            (u - q * v) % m
        }
    }

    public fun inverse_mod(n: u256, m: u256): Option<u256> {
        let (a, b) = (n, m);
        let (u, v) = (1_u256, 0_u256);

        while (b > 0) {
            let (q, r) = div_mod(a, b);
            (a, b) = (b, r);
            (u, v) = (v, mod_calc(u, q, v, m));
        };

        if (a == 1) {
            option::some((u % m))
        } else {
            option::none()
        }
    }

    public fun pow_mod(n: u256, exp: u256, m: Option<u256>): u256 {
        if (option::is_some(&m)) {
            let modulus= option::borrow(&m);
            ((pow(((n % *modulus) as u64), ((exp % *modulus) as u64))) as u256) % *modulus
        } else {
            ((pow((n as u64), (exp as u64))) as u256)
        }
    }

    #[test]
    fun generate_curve() {
        let p = 115792089237316195423570985008687907853269984665640564039457584007908834671663;
        let n = 115792089237316195423570985008687907852837564279074904382605163141518161494337;
        let generator = create_point(55066263022277343669578718895168534326250603453777594175500187360389116729240, 32670510020758816978083085130507043184471273380659243275938904335757337482424);
        let curve = create_curve(p, 0, 7, n, generator);
        let private_key = 42_u64;
        let public_key = mul(&curve, curve.generator, private_key);
        print(&private_key);
        print(&public_key);
        let hashed_message = aptos_hash::keccak256(b"this is a message");
        print(&hashed_message);

    }

    #[test]
    fun test_inverse_mod() {
        assert!(inverse_mod(7, 11) == some(8), 0);
        assert!(inverse_mod(161611711, 1033) == some(497), 0);
    }

    #[test]
    fun test_neg_mod() {
        assert!(mod_calc(8, 5, 2,17) == 15, 0);
        assert!(mod_calc(8, 6, 5,17) == 12, 0);
    }
}
