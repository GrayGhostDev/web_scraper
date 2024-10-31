# Imports
import os
import time
import re
import json
import logging
import streamlit as st
from typing import List, Optional, Dict
from collections import defaultdict

from selenium.webdriver.common.by import By
from selenium.common.exceptions import TimeoutException
import undetected_chromedriver as uc

from bs4 import BeautifulSoup
import requests

import spacy
from textblob import TextBlob
from fake_useragent import UserAgent
from tenacity import retry, stop_after_attempt, wait_fixed
from twocaptcha import TwoCaptcha

# Initialize logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Initialize SpaCy model
try:
    nlp = spacy.load("en_core_web_sm")
except OSError:
    import spacy.cli
    spacy.cli.download("en_core_web_sm")
    nlp = spacy.load("en_core_web_sm")


# Enhanced Content Extraction with NLP and HTML Parsing
class EnhancedContentExtractor:
    def analyze_text(self, text: str) -> dict:
        """Perform NLP analysis: entities, sentiment, topics."""
        doc = nlp(text)
        blob = TextBlob(text)

        # Named Entity Recognition
        entities = defaultdict(list)
        for ent in doc.ents:
            entities[ent.label_].append(ent.text)

        # Sentiment Analysis
        sentiment = {
            "polarity": blob.sentiment.polarity,
            "subjectivity": blob.sentiment.subjectivity
        }

        # Topic Modeling
        topics = [token.lemma_.lower() for token in doc if token.pos_ in ["NOUN", "PROPN"] and not token.is_stop]
        topic_freq = defaultdict(int)
        for topic in topics:
            topic_freq[topic] += 1

        top_topics = sorted(topic_freq.items(), key=lambda x: x[1], reverse=True)[:10]

        # Summary
        sentences = [sent.text for sent in doc.sents]
        summary = " ".join(sentences[:3])

        return {
            "entities": dict(entities),
            "sentiment": sentiment,
            "topics": dict(top_topics),
            "summary": summary
        }

    def parse_structured_data(self, soup: BeautifulSoup) -> dict:
        """Extract structured data from HTML."""
        return {
            "tables": self._parse_tables(soup),
            "lists": self._parse_lists(soup),
            "json_ld": self._extract_json_ld(soup)
        }

    def _parse_tables(self, soup: BeautifulSoup) -> List[dict]:
        tables = []
        for table in soup.find_all("table"):
            headers = [th.get_text(strip=True) for th in table.find_all("th")]
            rows = []
            for tr in table.find_all("tr"):
                row = [td.get_text(strip=True) for td in tr.find_all("td")]
                if row:
                    rows.append(row)
            tables.append({"headers": headers, "rows": rows})
        return tables

    def _parse_lists(self, soup: BeautifulSoup) -> dict:
        """Parse ordered and unordered lists."""
        lists = {"ordered": [], "unordered": []}
        for ul in soup.find_all("ul"):
            items = [li.get_text(strip=True) for li in ul.find_all("li")]
            lists["unordered"].append(items)
        for ol in soup.find_all("ol"):
            items = [li.get_text(strip=True) for li in ol.find_all("li")]
            lists["ordered"].append(items)
        return lists

    def _extract_json_ld(self, soup: BeautifulSoup) -> list:
        """Extract JSON-LD structured data."""
        json_ld = []
        for script in soup.find_all("script", type="application/ld+json"):
            try:
                json_data = json.loads(script.string)
                json_ld.append(json_data)
            except json.JSONDecodeError:
                continue
        return json_ld

    def extract_links(self, soup: BeautifulSoup) -> List[str]:
        """Extract all links from the page."""
        links = []
        for a_tag in soup.find_all("a", href=True):
            href = a_tag['href']
            if href.startswith('http'):
                links.append(href)
        return links

    def extract_images(self, soup: BeautifulSoup) -> List[str]:
        """Extract all image URLs from the page."""
        images = []
        for img_tag in soup.find_all("img", src=True):
            src = img_tag['src']
            if src.startswith('http'):
                images.append(src)
        return images

    def extract_article(self, url: str) -> dict:
        """Extract article content from a URL."""
        try:
            from newspaper import Article
        except ImportError:
            os.system("pip install newspaper3k")
            from newspaper import Article

        article = Article(url)
        article.download()
        article.parse()
        article.nlp()
        return {
            "title": article.title,
            "authors": article.authors,
            "publish_date": article.publish_date.isoformat() if article.publish_date else None,
            "text": article.text,
            "summary": article.summary,
            "keywords": article.keywords
        }


# Enhanced Proxy Management with CAPTCHA Solving
class EnhancedProxyManager:
    def __init__(self, captcha_api_key: str = None):
        self.user_agent = UserAgent()
        self.captcha_solver = TwoCaptcha(captcha_api_key) if captcha_api_key else None

    def solve_captcha(self, site_key: str, url: str) -> str:
        """Solve CAPTCHA using 2Captcha."""
        if not self.captcha_solver:
            raise ValueError("Captcha solver not configured")
        try:
            result = self.captcha_solver.recaptcha(sitekey=site_key, url=url)
            return result["code"]
        except Exception as e:
            logger.error(f"CAPTCHA solving failed: {str(e)}")
            return None

    def get_chrome_driver(self, use_proxy: bool = False, proxy: str = None) -> uc.Chrome:
        """Get undetected Chrome driver with anti-bot options."""
        options = uc.ChromeOptions()
        options.add_argument("--no-sandbox")
        options.add_argument("--disable-dev-shm-usage")
        options.add_argument(f"--user-agent={self.user_agent.random}")
        if use_proxy and proxy:
            options.add_argument(f"--proxy-server={proxy}")

        try:
            driver = uc.Chrome(options=options, use_subprocess=True)
            return driver
        except Exception as e:
            logger.error(f"Failed to initialize undetected Chrome WebDriver: {str(e)}")
            return None


# Enhanced Web Scraper with Anti-Bot Features
class EnhancedWebScraper:
    def __init__(self, captcha_api_key: str = None):
        self.content_extractor = EnhancedContentExtractor()
        self.proxy_manager = EnhancedProxyManager(captcha_api_key)

    def scrape_website(self, url: str, content_type: str) -> dict:
        driver = self.proxy_manager.get_chrome_driver()
        if not driver:
            logger.error("Failed to start the driver.")
            return None

        try:
            driver.get(url)
            time.sleep(3)  # Wait for page to load

            if "recaptcha" in driver.page_source.lower():
                site_key = self._extract_recaptcha_site_key(driver.page_source)
                if site_key:
                    captcha_response = self.proxy_manager.solve_captcha(site_key, url)
                    if captcha_response:
                        driver.execute_script(f"document.getElementById('g-recaptcha-response').innerHTML='{captcha_response}';")
                        driver.find_element(By.ID, "recaptcha-form").submit()
                        time.sleep(3)  # Wait after submitting CAPTCHA

            html = driver.page_source
            soup = BeautifulSoup(html, "html.parser")

            result = {
                "url": url,
                "content_type": content_type,
                "data": None,
                "nlp_analysis": None,
                "structured_data": None
            }

            # Extract content based on type
            if content_type == "text":
                text = soup.get_text(separator="\n", strip=True)
                result["data"] = text
                result["nlp_analysis"] = self.content_extractor.analyze_text(text)
            elif content_type == "links":
                links = self.content_extractor.extract_links(soup)
                result["data"] = links
            elif content_type == "images":
                images = self.content_extractor.extract_images(soup)
                result["data"] = images
            elif content_type == "article":
                article_data = self.content_extractor.extract_article(url)
                result["data"] = article_data
                result["nlp_analysis"] = self.content_extractor.analyze_text(article_data.get('text', ''))

            # Extract structured data
            result["structured_data"] = self.content_extractor.parse_structured_data(soup)
            return result

        except Exception as e:
            logger.error(f"Error scraping website: {str(e)}")
            return None
        finally:
            driver.quit()

    def _extract_recaptcha_site_key(self, html: str) -> Optional[str]:
        match = re.search(r'data-sitekey="([^"]+)"', html)
        return match.group(1) if match else None


# Streamlit UI for the Enhanced Web Scraper
def main():
    st.set_page_config(page_title="Enhanced Gray Ghost Scraper", page_icon="👻", layout="wide")

    st.markdown("""
        <style>
        .main {background-color: #FFFFF}
        .stButton>button {background-color: #4CAF50; color: black; font-weight: bold;}
        </style>
    """, unsafe_allow_html=True)

    with st.sidebar:
        st.title("👻 Gray Ghost Scraper")
        captcha_api_key = st.text_input("2Captcha API Key", type="password")
        st.header("🌐 Proxy & Anti-Bot Settings")
        proxy_type = st.selectbox("Proxy Type", ["None", "Custom Proxy"])
        proxy = None
        if proxy_type == "Custom Proxy":
            proxy = st.text_input("Proxy (e.g., http://user:pass@host:port)")
        use_proxy = proxy_type != "None"

        scraper = EnhancedWebScraper(captcha_api_key)

    st.title("🕸️ Web Scraping Configuration")
    url = st.text_input("Target URL")
    content_type = st.selectbox("Content Type", ["text", "links", "images", "article"])

    if st.button("🚀 Start Scraping"):
        if url:
            with st.spinner("Scraping in progress..."):
                result = scraper.scrape_website(url, content_type)
                if result:
                    st.success("✅ Scraping completed successfully!")
                    if content_type == "text":
                        st.subheader("Text Content")
                        st.text_area("Extracted Text", result.get('data', ''), height=200)
                        st.subheader("NLP Analysis")
                        st.json(result.get('nlp_analysis', {}))
                    elif content_type == "links":
                        st.subheader("Extracted Links")
                        st.write(result.get('data', []))
                    elif content_type == "images":
                        st.subheader("Extracted Images")
                        st.write(result.get('data', []))
                    elif content_type == "article":
                        st.subheader("Article Data")
                        st.json(result.get('data', {}))
                        st.subheader("NLP Analysis")
                        st.json(result.get('nlp_analysis', {}))
                    st.subheader("Structured Data")
                    st.json(result.get('structured_data', {}))
                else:
                    st.error("❌ Scraping failed. Please check the URL and try again.")
        else:
            st.warning("⚠️ Please enter a URL to scrape.")

if __name__ == "__main__":
    main()