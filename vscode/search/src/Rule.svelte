<script lang="ts">
  export let step: ProofStepInfo;
  export let previewClick: (uri: string, range: Range) => void;

  const rule = step.rule.toLowerCase();
  const source = step.source;
</script>

{#if source !== null}
  <span
    class="previewlink"
    on:click={() => previewClick(source.uri, source.range)}>{rule}</span
  >
{:else}
  <span>{rule}</span>
{/if}

<style>
  .previewlink {
    cursor: pointer;
  }

  .previewlink:hover {
    text-decoration: underline;
  }
</style>
