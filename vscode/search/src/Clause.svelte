<script lang="ts">
  export let clause: ClauseInfo;
  export let onClick: null | ((id: number) => void) = null;
  export let indent: number = 4;

  function spaces(n: number): string {
    return "\u00A0".repeat(n);
  }
</script>

{#if clause.id !== null}
  <span>
    {spaces(indent)}<span
      class="clause-link"
      on:click={() => {
        if (clause.id !== null && onClick !== null) {
          onClick(clause.id);
        }
      }}>{clause.text}</span
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
