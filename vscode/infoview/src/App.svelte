<script lang="ts">
  import { onMount } from "svelte";

  let heading = "Select a proposition to see its proof.";
  let lines: Array<string> = [];

  function handleDebugResponse(response: any) {
    if (response.message) {
      heading = response.message;
      lines = [];
      return;
    }

    heading = response.goalName;
    lines = response.output;
    if (response.completed) {
      lines.push("");
      lines.push("done.");
    }
  }

  onMount(() => {
    window.addEventListener("message", (event) => {
      handleDebugResponse(event.data);
    });
  });
</script>

<main>
  <h1>{heading}</h1>
  <pre>{lines.join("\n")}</pre>
</main>
