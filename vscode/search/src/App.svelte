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
  let nontrivial: Array<ProofStepInfo> = [];

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

    // New search responses also invalidate the info result
    searchResponse = response;
    infoResult = null;
    nontrivial = [];
    if (response.result !== null && response.result.steps !== null) {
      for (let step of response.result.steps) {
        if (step.trivial || stepsContain(nontrivial, step)) {
          continue;
        }
        nontrivial.push(step);
      }
    }
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
      searchResponse.result === null ||
      searchResponse.result.code === null ||
      searchResponse.result.code.length === 0
    ) {
      console.log("cannot insert proof");
      return;
    }
    vscode.postMessage({
      command: "insertProof",
      uri: searchResponse.uri,
      version: searchResponse.version,
      line: searchResponse.proofInsertionLine,
      addBlock: !searchResponse.hasBlock,
      code: searchResponse.result.code,
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
    {#if searchResponse.result !== null}
      {#if searchResponse.result.steps === null}
        <pre>No proof found.</pre>
      {:else if nontrivial.length === 0}
        <div class="mono">The proposition follows trivially.</div>
      {:else if searchResponse.result.code === null}
        <pre>Code generation failed:</pre>
        <pre>    {searchResponse.result.codeError}</pre>
      {:else if searchResponse.result.code.length === 0}
        <div class="mono">
          The proposition follows
          {#each nontrivial as step, i}
            {#if i > 0}
              {" and "}
            {/if}
            <Rule {step} {showLocation} />{/each}.
        </div>
      {:else}
        <pre>{["Proof found:\n"]
            .concat(searchResponse.result.code)
            .join("\n\t")
            .replace(/\t/g, spaces(4))}</pre>
        <button on:click={insertProof}>Insert proof</button>
      {/if}

      {#if searchResponse.result.steps !== null}
        <div class="mono">
          <br />
          The full proof has {pluralize(
            searchResponse.result.steps.length,
            "step"
          )}:
          <br />
          {#each searchResponse.result.steps as step}
            <br />
            <ProofStep {step} {clauseClick} {showLocation} />
          {/each}
        </div>
      {/if}
    {/if}
    <br />
    <hr />
    <div class="mono">
      <br />
      {#if infoResult === null}
        <span>Log output from the prover:</span>
        <pre>{"\n"}{searchResponse.textOutput.join("\n")}</pre>
      {:else}
        <ProofStep step={infoResult.step} {clauseClick} {showLocation} />
        <br />
        Consequences:<br />
        {#each infoResult.consequences as step}
          <br />
          <ProofStep {step} {clauseClick} {showLocation} />
        {/each}
      {/if}
    </div>
  {/if}
</main>
