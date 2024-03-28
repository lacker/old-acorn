<script lang="ts">
  export let step: ProofStepInfo;
  export let showLocation: (uri: string, range: Range) => void;

  const location = step.location;
</script>

{#if location !== null}
  from <span
    class="preview-link"
    on:click={() => showLocation(location.uri, location.range)}
    >{step.rule}</span
  >
{:else}
  by <span>{step.rule}</span>
{/if}

<style>
  .preview-link {
    cursor: pointer;
    color: var(--vscode-textLink-foreground);
  }

  .preview-link:hover {
    text-decoration: underline;
  }
</style>
