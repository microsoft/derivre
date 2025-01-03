/// Checks if there exists a sequence of n numbers A_0, ..., A_{n-1} such that
/// A_0 * 10^0 + ... + A_{n-1} * 10^{n-1} = remainder (mod divisor).
pub fn check_remainder(divisor: u32, remainder: u32, n: u32) -> bool {
    let remainder = remainder % divisor;

    if remainder == 0 {
        // Trivial
        true
    } else {
        let scale_multiplier = 10u32.pow(n);
        if scale_multiplier >= divisor {
            // n is large enough that we can guarantee a solution
            true
        } else if scale_multiplier - 1 < remainder {
            // We can't possibly reach remainder with n digits
            // Note this includes the case where n == 0 and remainder != 0
            false
        } else {
            true
        }
    }
}
