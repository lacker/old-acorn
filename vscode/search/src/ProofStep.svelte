<script lang="ts">
  export let step: ProofStepInfo;
  export let clauseClick: (id: number) => void;
  export let showLocation: (uri: string, range: Range) => void;
  import Clause from "./Clause.svelte";
  import Rule from "./Rule.svelte";

  function spaces(n: number): string {
    return "\u00A0".repeat(n);
  }
</script>

{#if step.clause.text === null}
  Contradiction, depth {step.depth}, <Rule {step} {showLocation} />.<br />
{:else if step.clause.id === null}
  An unactivated clause, depth {step.depth}, <Rule {step} {showLocation} />:<br
  />
  <Clause clause={step.clause} /><br />
{:else}
  Clause {step.clause.id}, depth {step.depth},
  <Rule {step} {showLocation} />:<br />
  <Clause clause={step.clause} onClick={clauseClick} />
  <br />
{/if}
{#each step.premises as [desc, clause]}
  {spaces(2)}using
  {#if clause.id !== null}
    clause {clause.id} as
  {/if}
  {desc}:<br />
  <Clause {clause} onClick={clauseClick} />
  <br />
{/each}
