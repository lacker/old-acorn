<script lang="ts">
  export let step: ProofStepInfo;
  export let clauseClick: (id: number | null) => void;

  function spaces(n: number): string {
    return "\u00A0".repeat(n);
  }
</script>

{#if step.clause.text === "<empty>"}
  Contradiction, by {step.rule.toLowerCase()}.<br />
{:else}
  {#if step.clause.id === null}
    By
  {:else}
    Clause {step.clause.id}, by
  {/if}
  {step.rule.toLowerCase()}:<br />
  <div class="clauselink" on:click={() => clauseClick(step.clause.id)}>
    {spaces(4)}<span class="underliney">{step.clause.text}</span>
  </div>
  <br />
{/if}
{#each step.premises as [desc, clause]}
  {spaces(2)}using clause {clause.id} as {desc}:<br />
  <div class="clauselink" on:click={() => clauseClick(clause.id)}>
    {spaces(4)}<span class="underliney">{clause.text}</span>
  </div>
  <br />
{/each}

<style>
  .clauselink {
    display: block;
    text-decoration: none;
    cursor: pointer;
    color: var(--vscode-textLink-foreground);
  }

  .clauselink:hover .underliney {
    text-decoration: underline;
  }
</style>
