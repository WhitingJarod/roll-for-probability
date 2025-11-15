import type * as WasmModule from "../public/pkg/rust_code";

let wasmInstance: typeof WasmModule | null = null;
let wasmPromise: Promise<typeof WasmModule> | null = null;

export async function loadWasm(): Promise<typeof WasmModule> {
  if (wasmInstance) {
    return wasmInstance;
  }

  if (!wasmPromise) {
    wasmPromise = (async () => {
      const wasmUrl = new URL("/pkg/rust_code.js", window.location.origin);
      const module = (await import(wasmUrl.href)) as typeof WasmModule;
      await module.default();
      wasmInstance = module;
      console.log("WASM initialized successfully");
      return module;
    })();
  }

  return wasmPromise;
}

export function getWasm(): typeof WasmModule | null {
  return wasmInstance;
}
