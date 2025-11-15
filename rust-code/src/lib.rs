use std::fmt::Display;

use hashbrown::HashMap;
use num_rational::Rational32;
use plotters::prelude::*;
use plotters_canvas::CanvasBackend;
use wasm_bindgen::prelude::*;

#[cfg(target_arch = "wasm32")]
use lol_alloc::{FreeListAllocator, LockedAllocator};
#[cfg(target_arch = "wasm32")]
use web_sys::HtmlCanvasElement;

#[cfg(target_arch = "wasm32")]
#[global_allocator]
static ALLOCATOR: LockedAllocator<FreeListAllocator> =
    LockedAllocator::new(FreeListAllocator::new());

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

#[cfg(target_arch = "wasm32")]
macro_rules! println {
    ($($t:tt)*) => (log(&format_args!($($t)*).to_string()));
}
#[cfg(target_arch = "wasm32")]
macro_rules! print {
    ($($t:tt)*) => (log(&format_args!($($t)*).to_string()));
}

#[wasm_bindgen]
#[derive(Clone)]
pub struct PMF {
    pmf: HashMap<i32, Rational32>,
}

#[wasm_bindgen]
impl PMF {
    pub fn empty() -> Self {
        PMF {
            pmf: HashMap::new(),
        }
    }

    pub fn from_dice_roll(sides: u8) -> Self {
        let sides = sides as i32;
        let mut pmf = HashMap::new();

        let prob = Rational32::new(1, sides);

        for i in 1..=sides {
            pmf.insert(i, prob);
        }

        PMF { pmf }
    }

    /// Adds two rolls or probabilities together and takes the sum
    pub fn add_pmf(&self, other: &Self) -> Self {
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

    /// Subtract rolls or probabilities together and takes the sum
    pub fn sub_pmf(&self, other: &Self) -> Self {
        let mut pmf = HashMap::new();

        for (val1, prob1) in self.pmf.iter() {
            for (val2, prob2) in other.pmf.iter() {
                let val = val1 + val2;
                let prob = prob1 * prob2;
                *(pmf.entry(val).or_default()) -= prob;
            }
        }

        PMF { pmf }
    }

    pub fn add_int(&self, other: i32) -> Self {
        let mut pmf = HashMap::new();
        for (val1, prob1) in self.pmf.iter() {
            let val = val1 + other;
            pmf.insert(val, *prob1);
        }
        PMF { pmf }
    }

    pub fn sub_int(&self, other: i32) -> Self {
        let mut pmf = HashMap::new();
        for (val1, prob1) in self.pmf.iter() {
            let val = val1 - other;
            pmf.insert(val, *prob1);
        }
        PMF { pmf }
    }

    pub fn expected(&self) -> Rational32 {
        let mut result = Rational32::new(0, 1);

        for (val, prob) in &self.pmf {
            result += prob * val;
        }

        result
    }

    pub fn is_at_most(&self, target: i32) -> Rational32 {
        let mut result = Rational32::new(0, 1);
        for (val, prob) in &self.pmf {
            if *val <= target {
                result += prob;
            }
        }
        result
    }

    pub fn is_at_least(&self, target: i32) -> Rational32 {
        let mut result = Rational32::new(0, 1);
        for (val, prob) in &self.pmf {
            if *val >= target {
                result += prob;
            }
        }
        result
    }

    pub fn is_greater_than(&self, target: i32) -> Rational32 {
        let mut result = Rational32::new(0, 1);
        for (val, prob) in &self.pmf {
            if *val > target {
                result += prob;
            }
        }
        result
    }

    pub fn is_less_than(&self, target: i32) -> Rational32 {
        let mut result = Rational32::new(0, 1);
        for (val, prob) in &self.pmf {
            if *val < target {
                result += prob;
            }
        }
        result
    }

    pub fn best_out_of(&self, rolls: u8) -> Self {
        if rolls == 0 {
            return PMF::empty();
        }

        let mut pmf = self.pmf.clone();
        let mut new_pmf = HashMap::new();

        for _ in 0..(rolls - 1) {
            for (val1, prob1) in &pmf {
                for (val2, prob2) in &self.pmf {
                    let val = val1.max(val2);
                    let prob = prob1 * prob2;
                    *(new_pmf.entry(*val).or_default()) += prob;
                }
            }
            std::mem::swap(&mut pmf, &mut new_pmf);
        }

        PMF { pmf }
    }

    pub fn worst_out_of(&self, rolls: u8) -> Self {
        if rolls == 0 {
            return PMF::empty();
        }

        let mut pmf = self.pmf.clone();
        let mut new_pmf = HashMap::new();

        for _ in 0..(rolls - 1) {
            for (val1, prob1) in &pmf {
                for (val2, prob2) in &self.pmf {
                    let val = val1.min(val2);
                    let prob = prob1 * prob2;
                    *(new_pmf.entry(*val).or_default()) += prob;
                }
            }
            std::mem::swap(&mut pmf, &mut new_pmf);
        }

        PMF { pmf }
    }

    pub fn repeat_and_sum(&self, reps: u8) -> Self {
        if reps == 0 {
            return PMF::empty();
        }

        let mut new = self.clone();

        for _ in 0..(reps - 1) {
            new = new.add_pmf(self);
        }

        new
    }

    pub fn to_string(&self) -> String {
        let mut out = String::new();

        let mut keys = self.pmf.keys().collect::<Vec<_>>();
        keys.sort();
        for (i, &val) in keys.iter().enumerate() {
            let prob = self.pmf[val];
            out.push_str(&format!(
                "{:>5} {:>5}/{:<5} ({:.2}%)",
                val,
                prob.numer(),
                prob.denom(),
                *prob.numer() as f64 / *prob.denom() as f64 * 100.0
            ));
            if i != keys.len() - 1 {
                out.push('\n');
            }
        }
        out
    }

    #[cfg(target_arch = "wasm32")]
    fn _render_web(
        &self,
        label: String,
        canvas: HtmlCanvasElement,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let backend = CanvasBackend::with_canvas_object(canvas).unwrap();

        let root = backend.into_drawing_area();
        root.fill(&WHITE)?;

        let mut data = Vec::new();
        for (val, &prob) in &self.pmf {
            data.push((val, *prob.numer() as f64 / *prob.denom() as f64));
        }
        data.sort_by(|i, j| i.0.partial_cmp(j.0).unwrap());
        let min_x = data.first().unwrap().0;
        let max_x = data.last().unwrap().0;
        let max_y = data.iter().map(|&(_, it)| it).fold(0.0, f64::max) * 100.0;

        let mut chart = ChartBuilder::on(&root)
            .margin(10)
            .x_label_area_size(60)
            .y_label_area_size(80)
            .build_cartesian_2d((*min_x as f64)..(*max_x as f64), 0.0..max_y)?;

        chart
            .configure_mesh()
            .disable_x_mesh()
            .bold_line_style(WHITE.mix(0.3))
            .y_desc("probability %")
            .x_desc(label)
            .axis_desc_style(("sans-serif", 30))
            .label_style(("sans-serif", 20))
            .draw()?;

        // chart.draw_series(
        //     Histogram::vertical(&chart)
        //         .style(RED.mix(0.5).filled())
        //         .data(data.iter().map(|&(&x, &y)| (x as f64, y * 100.0))),
        // )?;

        let pt = ((*min_x as f64).abs() + (*max_x as f64).abs()) / (1920 - 80) as f64;

        let width = 0.875;

        chart.draw_series(data.iter().map(|&(&x, y)| {
            let x = x as f64;
            let y = y * 100.0;
            Rectangle::new(
                [(x - width / 2.0, 0.0), (x + width / 2.0, y)],
                RED.mix(0.5).filled(),
            )
        }))?;

        let expected = self.expected();
        let expected = *expected.numer() as f64 / *expected.denom() as f64;

        chart.draw_series(std::iter::once(PathElement::new(
            vec![(expected, 0.0), (expected, max_y)],
            BLUE.stroke_width(2),
        )))?;

        chart.draw_series(std::iter::once(Text::new(
            format!("expected value: {:.2}", expected),
            (expected + 5.0 * pt, max_y),
            ("sans-serif", 30).into_font().color(&BLUE),
        )))?;

        Ok(())
    }

    #[cfg(target_arch = "wasm32")]
    pub fn render_web(&self, label: String, canvas: HtmlCanvasElement) -> Result<(), JsValue> {
        self._render_web(label, canvas).map_err(|e| e.to_string())?;
        Ok(())
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
                "\x1b[32m{:>5}\x1b[0m \x1b[32m{:>5}\x1b[0m/\x1b[32m{:<5}\x1b[0m (\x1b[32m{:.2}%\x1b[0m)",
                val,
                prob.numer(),
                prob.denom(),
                *prob.numer() as f64 / *prob.denom() as f64 * 100.0
            )?;
        }
        Ok(())
    }
}
