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
    class="clause-link"
    on:click={() => clause.id !== null && onClick(clause.id)}
  >
    {spaces(indent)}<span class="underliney">{clause.text}</span>
  </div>
{:else}
  <div class="non-link">
    {spaces(indent)}{clause.text}
  </div>
{/if}

<style>
  .non-link {
    display: block;
  }

  .clause-link {
    display: block;
    text-decoration: none;
    cursor: pointer;
    color: var(--vscode-textLink-foreground);
  }

  .clause-link:hover .underliney {
    text-decoration: underline;
  }
</style>
