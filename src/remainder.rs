/// Checks if there exists a sequence of n numbers A_0, ..., A_{n-1} such that
/// A_0 * 10^0 + ... + A_{n-1} * 10^{-1} = remainder (mod divisor)
pub fn check_remainder(divisor: u32, remainder: u32, n: u32) -> bool {
    // Normalize remainder
    let remainder = remainder % divisor;

    // Short circuit if we are out of digits
    if n == 0 {
        return remainder == 0;
    };
    // Short circuit if we can't possibly reach remainder
    if 10_u32.pow(n) - 1 < remainder {
        return false;
    }
    // Short circuit if n is sufficiently large
    if ((divisor as f32).log10().ceil() as u32) < n {
        return true;
    }

    // 1d DP table
    // current[rem] = true if `rem` is achievable
    let mut current = vec![false; divisor as usize];
    let mut next = vec![false; divisor as usize];
    current[0] = true; // 0 is always achievable

    for _ in 0..n {
        // Clear the 'next' array for the current iteration
        for entry in next.iter_mut() {
            *entry = false;
        }
        for rem in 0..divisor {
            if current[rem as usize] {
                for digit in 0..=9 {
                    let new_rem = (rem * 10 + digit) % divisor;
                    if new_rem == remainder {
                        // Short circuit if we've found a solution
                        return true;
                    }
                    next[new_rem as usize] = true;
                }
            }
        }
        // Swap 'current' and 'next' for the next iteration
        std::mem::swap(&mut current, &mut next);
    }
    false
}
