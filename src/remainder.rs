/// Checks if there exists a sequence of n numbers A_0, ..., A_{n-1} such that
/// A_0 * 10^0 + ... + A_{n-1} * 10^{n-1} = remainder (mod divisor)
pub fn check_remainder(divisor: u32, remainder: u32, n: u32) -> bool {
    // Normalize remainder
    let remainder = remainder % divisor;

    // Simple cases that don't require DP
    if let Some(result) = check_remainder_simple(divisor, remainder, n) {
        return result;
    }

    // 1d DP table
    // current[rem] = true if `rem` is achievable
    let mut current = vec![false; divisor as usize];
    let mut next = vec![false; divisor as usize];
    current[0] = true; // 0 is always achievable

    // Precompute 10^k for k from 0 to n-1
    let powers = precompute_powers(n);

    for i in 0..n {
        // Clear the 'next' array for the current iteration
        for entry in next.iter_mut() {
            *entry = false;
        }
        for rem in 0..divisor {
            if current[rem as usize] {
                for digit in 0..=9 {
                    let new_n = n - i - 1;
                    let new_rem = (rem + digit * powers[new_n as usize]) % divisor;
                    let remainder_to_go = (remainder + divisor - new_rem) % divisor;
                    match check_remainder_simple(divisor, remainder_to_go, new_n) {
                        // Guaranteed solution, no need to continue
                        Some(true) => return true,
                        // Prune this branch; it's a dead end
                        Some(false) => {}
                        // Continue with DP
                        None => next[new_rem as usize] = true,
                    }
                }
            }
        }
        // Swap 'current' and 'next' for the next iteration
        std::mem::swap(&mut current, &mut next);
    }
    false
}

fn check_remainder_simple(divisor: u32, remainder: u32, n: u32) -> Option<bool> {
    if remainder == 0 {
        // Trivial
        Some(true)
    } else if 10_u32.pow(n) - 1 < remainder {
        // We can't possibly reach remainder with n digits
        // Note this includes the case where n == 0 and remainder != 0
        Some(false)
    } else if ((divisor as f32).log10().ceil() as u32) < n {
        // n is large enough that we can guarantee a solution
        Some(true)
    } else {
        // No guarantee either way -- need to use DP
        None
    }
}

/// Precompute 10^k for k from 0 to n-1
fn precompute_powers(n: u32) -> Vec<u32> {
    let mut powers = vec![1; n as usize];
    for i in 1..n as usize {
        powers[i] = powers[i - 1] * 10;
    }
    powers
}
