import "./app.css";
import App from "./App.svelte";

const target = document.getElementById("app");
const app = target === null ? null : new App({ target });

export default app;
