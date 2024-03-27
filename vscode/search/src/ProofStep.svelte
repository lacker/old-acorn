<script lang="ts">
  export let step: ProofStepInfo;
  export let clauseClick: (id: number) => void;
  export let previewClick: (uri: string, range: Range) => void;
  import ClauseLink from "./ClauseLink.svelte";
  import Rule from "./Rule.svelte";

  function spaces(n: number): string {
    return "\u00A0".repeat(n);
  }
</script>

{#if step.clause.text === "<empty>"}
  Contradiction, by <Rule {step} {previewClick} />.<br />
{:else}
  {#if step.clause.id === null}
    By
  {:else}
    Clause {step.clause.id}, by
  {/if}
  <Rule {step} {previewClick} />:<br />
  <ClauseLink clause={step.clause} onClick={clauseClick} />
  <br />
{/if}
{#each step.premises as [desc, clause]}
  {spaces(2)}using clause {clause.id} as {desc}:<br />
  <ClauseLink {clause} onClick={clauseClick} />
  <br />
{/each}
