#![allow(unused)]

use std::fmt::Display;

use hashbrown::HashMap;
use num_rational::Rational32;

#[derive(Clone, Debug)]
struct PMF {
    pmf: HashMap<i32, Rational32>,
}

impl PMF {
    fn empty() -> Self {
        PMF {
            pmf: HashMap::new(),
        }
    }

    fn from_dice_roll(sides: u8) -> Self {
        let sides = sides as i32;
        let mut pmf = HashMap::new();

        let prob = Rational32::new(1, sides);

        for i in 1..=sides {
            pmf.insert(i, prob);
        }

        PMF { pmf }
    }

    /// Adds two rolls or probabilities together and takes the sum
    fn convolve(&self, other: &Self) -> Self {
        let mut pmf = HashMap::new();

        for (val1, prob1) in self.pmf.iter() {
            for (val2, prob2) in other.pmf.iter() {
                let val = val1 + val2;
                let prob = prob1 * prob2;
                *(pmf.entry(val).or_default()) += prob;
            }
        }

        PMF { pmf }
    }

    fn repeat_and_sum(&self, reps: u8) -> Self {
        if reps == 0 {
            return PMF::empty();
        }

        let mut new = self.clone();

        for _ in 0..(reps - 1) {
            new = new.convolve(self);
        }

        new
    }
}

impl Display for PMF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut keys = self.pmf.keys().collect::<Vec<_>>();
        keys.sort();
        for val in keys {
            let prob = self.pmf[val];
            writeln!(
                f,
                "\x1b[32m{:>5}\x1b[0m \x1b[32m{:>5}\x1b[0m/\x1b[32m{:<5}\x1b[0m (\x1b[32m{:.4}%\x1b[0m)",
                val,
                prob.numer(),
                prob.denom(),
                *prob.numer() as f64 / *prob.denom() as f64
            )?;
        }
        Ok(())
    }
}

fn main() {
    let d6_roll = PMF::from_dice_roll(6);
    println!("{}", d6_roll);
    // let convolved = d6_roll.convolve(&d6_roll);
    // println!("{:#?}", convolved);
    let sum_of_three = d6_roll.repeat_and_sum(3);
    println!("\n\n\n{}", sum_of_three);
}
