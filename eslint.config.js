import js from "@eslint/js";
import globals from "globals";

export default [
  { ignores: ["assets/"] },
  js.configs.recommended,
  { languageOptions: { globals: globals.browser } },
];
