<script context="module">
  let vscode = acquireVsCodeApi();
</script>

<script lang="ts">
  import { onMount } from "svelte";

  // handleSearchResponse sets each of these each time it's called.
  let heading = "Select a proposition to see its proof.";
  let complete: boolean = false;
  let lines: string[] = [];
  let code: string[] | null = null;
  let proof_insertion_line: number | null = null;

  // NOTE: the 'response' type corresponds to SearchResponse in language_server.rs.
  function handleSearchResponse(response: any) {
    if (response.message) {
      heading = "message: " + response.message;
      complete = false;
      lines = [];
      code = null;
      proof_insertion_line = null;
      return;
    }

    heading = response.goalName;
    lines = response.lines;
    if (response.result) {
      complete = true;
      code = response.result.code;
      proof_insertion_line = response.proof_insertion_line;
      lines.push("");
      lines.push("(end of output)");
    } else {
      complete = false;
      code = null;
      proof_insertion_line = null;
    }
  }

  onMount(() => {
    window.addEventListener("message", (event) => {
      handleSearchResponse(event.data);
    });
  });

  function insertProof() {
    if (
      !complete ||
      code === null ||
      code.length === 0 ||
      proof_insertion_line === null
    ) {
      console.log("cannot insert proof");
      return;
    }
    vscode.postMessage({
      command: "insertProof",
      line: proof_insertion_line,
      code,
    });
  }
</script>

<main>
  <h1>{heading}</h1>

  {#if complete}
    {#if code === null}
      <pre>proof search failed.</pre>
    {:else if code.length === 0}
      <pre>the proof is trivial.</pre>
    {:else}
      <pre>{"proof found:\n  " + code.join("\n  ")}</pre>
      <button on:click={insertProof}>Insert proof</button>
    {/if}
  {/if}

  <pre>{lines.join("\n")}</pre>
</main>
