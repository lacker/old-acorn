<script lang="ts">
  import { onMount } from "svelte";

  let heading = "Select a proposition to see its proof.";
  let lines: Array<string> = [];
  let result: any = null;

  function handleSearchResponse(response: any) {
    if (response.message) {
      heading = response.message;
      lines = [];
      return;
    }

    heading = response.goalName;
    lines = response.lines;
    result = response.result;
    if (response.result) {
      lines.push("");
      lines.push("(end of output)");
    }
  }

  onMount(() => {
    window.addEventListener("message", (event) => {
      handleSearchResponse(event.data);
    });
  });
</script>

<main>
  <h1>{heading}</h1>
  <pre>{lines.join("\n")}</pre>
</main>
