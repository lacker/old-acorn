<script lang="ts">
  export let clause: ClauseInfo;
  export let onClick: (id: number) => void;
  export let indent: number = 4;

  const id = clause.id;

  function spaces(n: number): string {
    return "\u00A0".repeat(n);
  }
</script>

{#if id !== null}
  <span>
    {spaces(indent)}<span class="clause-link" on:click={() => onClick(id)}
      >{clause.text}</span
    >
  </span>
{:else}
  <span>
    {spaces(indent)}{clause.text}
  </span>
{/if}

<style>
  .clause-link {
    cursor: pointer;
  }

  .clause-link:hover {
    text-decoration: underline;
  }
</style>
