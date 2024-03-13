<script context="module">
  let vscode = acquireVsCodeApi();
</script>

<script lang="ts">
  import { onMount } from "svelte";

  // This will be updated to reflect the last successful search response.
  let searchResponse: SearchResponse | null = null;

  function handleSearchResponse(response: SearchResponse) {
    if (response.error || response.goalName === null) {
      // Error responses should not reach this point.
      console.error("unexpected upstream error:", response.error);
      return;
    }

    searchResponse = response;
  }

  onMount(() => {
    window.addEventListener("message", (event) => {
      handleSearchResponse(event.data);
    });
  });

  function insertProof() {
    if (
      searchResponse === null ||
      searchResponse.result === null ||
      searchResponse.result.code === null ||
      searchResponse.result.code.length === 0 ||
      searchResponse.proofInsertionLine === null
    ) {
      console.log("cannot insert proof");
      return;
    }
    vscode.postMessage({
      command: "insertProof",
      uri: searchResponse.uri,
      version: searchResponse.version,
      line: searchResponse.proofInsertionLine,
      code: searchResponse.result.code,
    });
  }
</script>

<main>
  {#if searchResponse === null || searchResponse.goalName === null}
    <h1>Select a proposition to see its proof.</h1>
  {:else}
    <h1>{searchResponse.goalName}</h1>

    {#if searchResponse.result !== null}
      {#if searchResponse.result.code === null}
        <pre>proof search failed.</pre>
      {:else if searchResponse.result.code.length === 0}
        <pre>the proof is trivial.</pre>
      {:else}
        <pre>{"proof found:\n  " +
            searchResponse.result.code.join("\n  ")}</pre>
        <button on:click={insertProof}>Insert proof</button>
      {/if}

      {#if searchResponse.result.steps !== null}
        {#each searchResponse.result.steps as step}
          <pre>{step.clause.id === null
              ? "Contradiction"
              : `Clause ${step.clause.id}`}, by {step.rule.toLowerCase()}:

{step.clause.text}</pre>
        {/each}
      {/if}
    {/if}

    <pre>{searchResponse.textOutput.join("\n")}</pre>
  {/if}
</main>
