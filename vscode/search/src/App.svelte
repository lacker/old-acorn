<script context="module">
  let vscode = acquireVsCodeApi();
</script>

<script lang="ts">
  import { onMount } from "svelte";
  import Goal from "./Goal.svelte";
  import ProofStep from "./ProofStep.svelte";
  import Rule from "./Rule.svelte";

  // These are updated to reflect the last valid responses from the extension.
  let searchResponse: SearchResponse | null = null;
  let infoResult: InfoResult | null = null;

  function stepsContain(
    steps: Array<ProofStepInfo>,
    step: ProofStepInfo
  ): boolean {
    for (let s of steps) {
      if (
        s.rule === step.rule &&
        JSON.stringify(step.location) === JSON.stringify(s.location)
      ) {
        return true;
      }
    }
    return false;
  }

  function handleSearchResponse(response: SearchResponse) {
    if (response.failure || response.goalName === null) {
      // Failure responses should not reach this point.
      console.error("unexpected upstream failure:", response.failure);
      return;
    }

    if (searchResponse !== null && searchResponse.id !== response.id) {
      // Invalidate the info result
      infoResult = null;
    }

    searchResponse = response;
  }

  function handleInfoResponse(response: InfoResponse) {
    // Only accept info responses that match the current search response.
    if (
      searchResponse === null ||
      response.result === null ||
      response.searchId != searchResponse.id
    ) {
      return;
    }
    infoResult = response.result;
  }

  onMount(() => {
    window.addEventListener("message", (event) => {
      if (event.data.type === "search") {
        handleSearchResponse(event.data.response);
        return;
      }
      if (event.data.type === "info") {
        handleInfoResponse(event.data.response);
        return;
      }
      console.error("unexpected message type:", event.data.type);
    });
  });

  function insertProof() {
    if (
      searchResponse === null ||
      searchResponse.status.code === null ||
      searchResponse.status.code.length === 0
    ) {
      console.log("cannot insert proof");
      return;
    }
    vscode.postMessage({
      command: "insertProof",
      uri: searchResponse.uri,
      version: searchResponse.version,
      line: searchResponse.proofInsertionLine,
      insertBlock: searchResponse.insertBlock,
      code: searchResponse.status.code,
    });
  }

  function spaces(n: number): string {
    return "\u00A0".repeat(n);
  }

  function clauseClick(id: number) {
    if (searchResponse === null) {
      return;
    }
    let params: InfoParams = {
      searchId: searchResponse.id,
      clauseId: id,
    };
    vscode.postMessage({ command: "infoRequest", params });
  }

  function randomClause() {
    if (searchResponse === null || searchResponse.status.numActivated === 0) {
      return;
    }

    // Pick a random activated clause
    let id = Math.floor(Math.random() * searchResponse.status.numActivated);
    clauseClick(id);
  }

  function showLocation(uri: string, range: Range) {
    vscode.postMessage({ command: "showLocation", uri, range });
  }

  function pluralize(n: number, noun: string): string {
    let word = n === 1 ? noun : noun + "s";
    return `${n} ${word}`;
  }
</script>

<main>
  {#if searchResponse === null || searchResponse.goalName === null}
    <h1><pre>Select a proposition to see its proof.</pre></h1>
  {:else}
    <Goal {searchResponse} {showLocation} />
    <hr />
    <br />
    {#if searchResponse.status.outcome === null}
      <pre>Working...</pre>
    {:else if searchResponse.status.outcome === "Inconsistent"}
      <pre>Local assumptions are inconsistent.</pre>
      <pre>If this is a proof by contradiction, put a `false` at the end of this block.</pre>
      <pre>If there shouldn't be a contradiction, please report a bug!</pre>
    {:else if !searchResponse.status.needsSimplification}
      <pre>The proposition follows trivially.</pre>
    {:else if searchResponse.status.code === null}
      <pre>Error during code generation:</pre>
      <pre>    {searchResponse.status.codeError}</pre>
    {:else if searchResponse.status.code.length === 0}
      <pre>We found a proof, but it needs to be simplified, and we couldn't
           decide how to simplify it. Sorry!</pre>
    {:else if searchResponse.status.steps === null}
      <pre>We could not find a proof.</pre>
    {:else}
      <pre>{["The proof needs to be simplified. Try this:\n"]
          .concat(searchResponse.status.code)
          .join("\n\t")
          .replace(/\t/g, spaces(4))}</pre>
      <button on:click={insertProof}>Insert code</button>
    {/if}

    {#if searchResponse.status.steps !== null}
      <div class="mono">
        <br />
        The full proof has {pluralize(
          searchResponse.status.steps.length,
          "step"
        )}:
        <br />
        {#each searchResponse.status.steps as step}
          <br />
          <ProofStep {step} {clauseClick} {showLocation} />
        {/each}
      </div>
    {/if}
    <br />
    <hr />
    <div class="mono">
      <br />
      <button
        on:click={() => {
          infoResult = null;
        }}>Statistics</button
      >
      <button on:click={randomClause}>Random clause</button>
      <br /><br />
      {#if infoResult === null}
        <span
          >Prover status: {searchResponse.status.outcome === null
            ? "Working..."
            : searchResponse.status.outcome}</span
        >
        <br />
        <span>Activated clauses: {searchResponse.status.numActivated}</span>
      {:else}
        <ProofStep step={infoResult.step} {clauseClick} {showLocation} />
        <br />
        {#if infoResult.consequences.length === 0}
          There are no consequences.
        {:else}
          Consequences:<br />
          {#each infoResult.consequences as step}
            <br />
            <ProofStep {step} {clauseClick} {showLocation} />
          {/each}
          {#if infoResult.numConsequences > infoResult.consequences.length}
            <br />
            Truncated. Showing {infoResult.consequences.length} out of {infoResult.numConsequences}
            clauses.
          {/if}
        {/if}
      {/if}
    </div>
  {/if}
</main>
