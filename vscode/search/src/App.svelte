<script context="module">
  let vscode = acquireVsCodeApi();
</script>

<script lang="ts">
  import { onMount } from "svelte";

  // handleSearchResponse typically sets each of these each time it's called.
  let heading = "Select a proposition to see its proof.";
  let complete: boolean = false;
  let textOutput: string[] = [];
  let code: string[] | null = null;
  let proofInsertionLine: number | null = null;
  let uri: string | null;
  let version: number | null;

  // NOTE: the 'response' type corresponds to SearchResponse in language_server.rs.
  function handleSearchResponse(response: any) {
    if (response.error) {
      // Error responses should not reach this point.
      console.error("unexpected upstream error:", response.error);
      return;
    }

    heading = response.goalName;
    textOutput = response.textOutput;
    uri = response.uri;
    version = response.version;
    if (response.result) {
      complete = true;
      code = response.result.code;
      proofInsertionLine = response.proofInsertionLine;
      textOutput.push("");
      textOutput.push("(end of output)");
    } else {
      complete = false;
      code = null;
      proofInsertionLine = null;
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
      proofInsertionLine === null
    ) {
      console.log("cannot insert proof");
      return;
    }
    vscode.postMessage({
      command: "insertProof",
      uri,
      version,
      line: proofInsertionLine,
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

  <pre>{textOutput.join("\n")}</pre>
</main>
