/**
 * This file is the entry point for the React app, it sets up the root
 * element and renders the App component to the DOM.
 *
 * It is included in `src/index.html`.
 */

import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import CustomNodeFlow from "./App.tsx";

import "./index.css";

const app = (
  <StrictMode>
    <CustomNodeFlow />
  </StrictMode>
);

const rootElement = document.getElementById("root");
if (rootElement) {
  createRoot(rootElement).render(app);
}
