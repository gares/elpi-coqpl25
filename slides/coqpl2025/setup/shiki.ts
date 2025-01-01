import type { ShikiSetupReturn } from '@slidev/types'
import { defineShikiSetup } from '@slidev/types'
import Elpi from './elpi.tmLanguage.json'
import Coq from './coq.tmLanguage.json'

export default defineShikiSetup((): ShikiSetupReturn => {
  return {
    langs: [
      'ts',
      'js',
      'vue',
      'html',
      'yaml',
      'md',
      'markdown',
      Coq,
      Elpi,
    ],
  }
})