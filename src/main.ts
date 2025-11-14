import { createApp } from "vue";
import App from "./App.vue";

import init, { PMF } from "../rust-code/pkg/rust_code";

async function main() {
  await init();

  const d4 = PMF.from_dice_roll(4);
  const d6 = PMF.from_dice_roll(6);
  const sum = d4.add_pmf(d6);
  console.log("PMF of rolling a d4 and a d6 and summing the results:");
  console.log(sum.to_string());

  createApp(App).mount("#app");
}

main();
