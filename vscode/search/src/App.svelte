<script lang="ts">
  import { onMount } from "svelte";

  let heading = "Select a proposition to see its proof.";
  let lines: Array<string> = [];
  let result: any = null;

  // NOTE: the 'response' type corresponds to SearchResponse in language_server.rs.
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

  function insertProof() {
    if (!result || !result.code) {
      return;
    }
    const vscode = acquireVsCodeApi();
    vscode.postMessage({
      command: "insertProof",
      code: result.code,
    });
  }
</script>

<main>
  <h1>{heading}</h1>

  {#if result}
    {#if result.code}
      {#if result.code.length === 0}
        <pre>the proof is trivial.</pre>
      {:else}
        <pre>{"proof found:\n  " + result.code.join("\n  ")}</pre>
        <button on:click={insertProof}>Insert proof</button>
      {/if}
    {:else}
      <pre>proof search failed.</pre>
    {/if}
  {/if}

  <pre>{lines.join("\n")}</pre>
</main>
