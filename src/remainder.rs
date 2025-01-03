/// Checks if there exists a sequence of n numbers A_0, ..., A_{n-1} such that
/// A_0 * 10^0 + ... + A_{n-1} * 10^{n-1} = remainder (mod divisor).
/// Returns a boolean indicating whether such a sequence exists, and the cost of the solution
/// expressed as the number of checks performed.
pub fn check_remainder(divisor: u32, remainder: u32, n: u32) -> (bool, usize) {
    let mut cost: usize = 1;

    // Normalize remainder
    let remainder = remainder % divisor;

    // Simple cases that don't require DP
    if let Some(result) = check_remainder_simple(divisor, remainder, n) {
        return (result, cost);
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
        next.fill(false);
        for rem in 0..divisor {
            if current[rem as usize] {
                for digit in 0..=9 {
                    let new_n = n - i - 1;
                    let new_rem = (rem + digit * powers[new_n as usize]) % divisor;
                    if let Some(elt) = next.get_mut(new_rem as usize) {
                        if !*elt {
                            cost += 1;
                            let remainder_to_go = (remainder + divisor - new_rem) % divisor;
                            match check_remainder_simple(divisor, remainder_to_go, new_n) {
                                // Found a solution
                                Some(true) => return (true, cost),
                                // Prune this branch; it's a dead end
                                Some(false) => {}
                                // Continue with DP
                                None => *elt = true,
                            }
                        }
                    } else {
                        // This should never happen
                        unreachable!();
                    }
                }
            }
        }
        // Swap 'current' and 'next' for the next iteration
        std::mem::swap(&mut current, &mut next);
    }
    (false, cost)
}

#[inline]
fn check_remainder_simple(divisor: u32, remainder: u32, n: u32) -> Option<bool> {
    if remainder == 0 {
        // Trivial
        Some(true)
    } else {
        let scale_multiplier = 10u32.pow(n);
        if scale_multiplier >= divisor {
            // n is large enough that we can guarantee a solution
            Some(true)
        } else if scale_multiplier - 1 < remainder {
            // We can't possibly reach remainder with n digits
            // Note this includes the case where n == 0 and remainder != 0
            Some(false)
        } else {
            // No guarantee either way -- need to use DP
            None
        }
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
