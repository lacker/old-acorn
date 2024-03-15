<script lang="ts">
  export let clause: ClauseInfo;
  export let onClick: (id: number) => void;
  export let indent: number = 4;

  function spaces(n: number): string {
    return "\u00A0".repeat(n);
  }
</script>

{#if clause.id !== null}
  <div
    class="clauselink"
    on:click={() => clause.id !== null && onClick(clause.id)}
  >
    {spaces(indent)}<span class="underliney">{clause.text}</span>
  </div>
{:else}
  <div class="nonlink">
    {spaces(indent)}{clause.text}
  </div>
{/if}

<style>
  .nonlink {
    display: block;
  }

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
